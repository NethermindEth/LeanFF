import FF.CoCoA
import FF.MTacM
import FF.Normalise
import FF.LCocoaParser
import FF.Translate
import Qq
import FF.RemoveIneqs

open Lean Qq Parser Tactic Elab Term

namespace EzPz

open CoCoA

lemma R {n : ℕ} {x w : ZMod n} {c : ZMod n} (h₁ : x = 0) (h₂ : w = 0) : x - c * w = 0 := by
  grind

lemma S {n : ℕ} {x w : ZMod n} {c₁ c₂ : ZMod n} (h₁ : x = 0) (h₂ : w = 0) : x * c₁ - w * c₂ = 0 := by
  grind

open PrettyPrinter Delaborator in
def lhsOfHyp (name : Name) : MTacM Term := withMainContext do
  let .some hyp := (←getLCtx).findFromUserName? name
    | throwError "{name} is not in the local context."
  let hyp ← instantiateMVars hyp.type
  let_expr Eq _ lhs _ := hyp
    | throwError "Expected `lhs = 0`. Got: {hyp}"
  delab lhs

def termOfCocoaPoly (poly : String) : MTacM Term := do
  let .ok polyStx := runParserCategory (←getEnv) `term poly
    | throwError "{poly} is not a valid ZMod equation."
  pure ⟨polyStx⟩

def CoCoA.Ast.Cocoa.lhsOfPoly (cocoa : Ast.Cocoa) (idx : ℕ) : MTacM Term := do
  let .some poly := cocoa.polynomialOfIdx idx
    | throwError "{idx} not in {repr cocoa}."
  termOfCocoaPoly poly

def reconcilePoliesAt (lhs rhs : Term) (loc : Ident) : MTacM Unit := do
  runTacticInΓ (←`(tactic|rw [show $lhs = $rhs by grind] at $loc:ident))

open PrettyPrinter Delaborator in
def CoCoA.Ast.Cocoa.toPolyMap (cocoa : Ast.Cocoa) : MTacM SyncMap := withMainContext do
  withTraceNode `EzPz.Tactic.ff.trace.initPolies
                (return m!"{exceptEmoji ·} Initial system reconciliation.") do
  cocoa.polynomials.foldlM (init := ⟨{}, {}⟩) fun acc poly ↦ do
    let ⟨idx, poly, .some name⟩ := poly | pure acc
    reconcilePoliesAt (←lhsOfHyp name) (←termOfCocoaPoly poly) (mkIdent name)
    pure {acc with st := acc.st.insert idx name}

open PrettyPrinter Delaborator in
/--
Executes the semantics associated with the reduction `reduction`.
-/
def CoCoA.Ast.Reduction.run (map : SyncMap)
                            (freshName : Ident)
                            (reduction : Ast.Reduction)
                            (targetPoly : Term) : MTacM Unit := withMainContext do
  let name := map.identOfIdx reduction.source
  runTacticInΓ (←`(tactic|(have $freshName := $name)))
  match reduction with
  | .M .. =>
    trace[EzPz.Tactic.ff.trace.reduction.M] "Normalising."
    reconcilePoliesAt (← lhsOfHyp freshName.getId) targetPoly freshName
  | .R _ _ reductions =>
    trace[EzPz.Tactic.ff.trace.reduction.R] "{repr reductions}"
    discard <| reductions.mapM fun it@⟨n, _⟩ ↦ do
      let n := map.identOfIdx n
      let (_, term) ← it.toStx
      trace[EzPz.Tactic.ff.debug.reduction.R] "{←debugOfIdent freshName}"
      runTacticInΓ (←`(tactic|replace $freshName := EzPz.R (c := $term) $freshName $n))
    withMainContext do
      trace[EzPz.Tactic.ff.debug.reduction.R] "{←debugOfIdent freshName}"
    reconcilePoliesAt (← lhsOfHyp freshName.getId) targetPoly freshName
  | .S it₁ it₂@⟨n, _⟩ _ =>
    trace[EzPz.Tactic.ff.trace.reduction.S] "{repr it₁} | {repr it₂}"
    let n := map.identOfIdx n
    let (_, tsrc) ← it₁.toStx
    let (_, tred) ← it₂.toStx
    debugBracketHypOfLoc (←`(location|at $freshName:ident)) `EzPz.Tactic.ff.debug.reduction.S do
    runTacticInΓ (←`(tactic|replace $freshName := EzPz.S (c₁ := $tsrc) (c₂ := $tred) $name $n))
  where debugOfIdent (idn : Ident) : MTacM String := do
    debugHypsOfLoc (←`(location|at $idn:ident))

partial def creepyCrawlie (smtout : Ast.Cocoa)
                          (initial : SyncMap) : MTacM (SyncMap × Name) := withMainContext do
  /-
  ``ineq` chosen arbitrarily, we either replace this or error out gracefully regardless.
  -/
  smtout.reductions.foldlM processReduction (initial, `ineq)
  where
    updateEnv (reduction : Ast.Reduction) (map : SyncMap) : MTacM (SyncMap × Name) := do
      let freshName ← withMainContext (Meta.getUnusedUserName reduction.simpleName)
      reduction.run map (mkIdent freshName) (←smtout.lhsOfPoly reduction.target)
      return (map.associate reduction.target freshName, freshName)

    processReduction (map : SyncMap × Name) (reduction : Ast.Reduction) : MTacM (SyncMap × Name) := do
      if map.1.seen.contains reduction then return map
      let map ← reduction.dependencies.foldlM (init := (map.1.visit reduction, map.2))
        fun map dependency ↦ do
          if map.1.st[dependency]?.isSome then return map
          let .some targetReduction := smtout.reductionOfTarget dependency
            | throwError s!"Cannot construct polynomial {dependency} as it is not a \
                            target of any of the reductions in {repr smtout.reductions} \
                            nor is it one of the polynomials in the map {repr map.1.st}."
          processReduction map targetReduction
      let (map', name) ← updateEnv reduction map.1
      pure (map.1.union map', name)

open CoCoA

open Elab Tactic in
def hashGoal (goal : MVarId) : MetaM UInt64 := do
  let fullGoal :=
    ppGoal
      (MessageData.mkPPContext
        {currNamespace := `anonymous, openDecls := []}
        {env := ←getEnv, mctx := ←getMCtx, lctx := ←getLCtx, opts := default}) goal
  return (←fullGoal).pretty.hash

def CVC5Command (input : System.FilePath) : MetaM IO.Process.SpawnArgs := do
  let opts ← getOptions
  pure {
    cmd := opts.getString `EzPz.cvc5cmd
    env := #[("LD_LIBRARY_PATH", opts.getString `EzPz.cvc5lib)]
    args := #[input.toString]
  }

def translateToCVC5 (goal : MVarId) : MetaM System.FilePath := do
  let smt2lib : System.FilePath := s!"{←hashGoal goal}"
  let smt2libContents ← extractSmtLib goal
  trace[EzPz.Tactic.ff.debug.smt] "smt2-lib in {smt2lib}:\n{smt2libContents}"
  IO.FS.writeFile smt2lib smt2libContents
  return smt2lib

def cocoaOfCVC5 (goal : MVarId) : TermElabM Ast.Cocoa := goal.withContext do
  withTraceNode `EzPz.Tactic.ff.trace (return m!"{exceptEmoji ·} Call SMT.") do
  let filename ← translateToCVC5 goal
  try
    let cocoa ← IO.Process.run (←CVC5Command filename)
    trace[EzPz.Tactic.ff.debug.smt] "SMT out:\n{cocoa}"
    match Parser.runParserCategory (←getEnv) `term s!"[CoCoA|{cocoa}]" with
    | .ok stx => let `([CoCoA|$_cocoa]) := stx | throwError "Malformed CoCoA: {cocoa}"
                 unsafe Elab.Term.evalTerm Ast.Cocoa q(Ast.Cocoa) stx
    | .error e => throwError "Cannot parse CVC5 output.\nInner error: {e}"    
  finally
    IO.FS.removeFile filename

set_option hygiene false in
def finiteFieldCVC : MTacM Unit := withMainContext do
  let initialPolies ← (←get).cocoa.toPolyMap
  let resultIn ←
    withTraceNode `EzPz.Tactic.ff.trace.reduction (return m!"{exceptEmoji ·} Reductions.") do
      Prod.snd <$> creepyCrawlie (←get).cocoa initialPolies
  trace[EzPz.Tactic.ff.debug.resultHyp] "Result in: {resultIn}"
  try
    /-
    NB this is really just `grind`.
    We do, in two steps, for `poly = 0`:
    - show `poly = 1`
    - discharge `1 ≠ 0`
    -/
    reconcilePoliesAt (← lhsOfHyp resultIn) (←`((1 : ZMod _))) (mkIdent resultIn)
    runTacticInΓ (←(`(tactic|simp only [one_ne_zero] at $(mkIdent resultIn):ident)))
  catch _ => logInfo m!"FF failed - {resultIn} is not a contradiction."

section

open Elab Tactic

set_option hygiene false

def tryNegateConclusion : TacticM Unit := Tactic.withMainContext do
  /-
  Try handling `_ ≠ _`.
  -/
  let targetName ← Meta.getUnusedUserName `target
  evalTactic (←(`(tactic|try intros $(mkIdent targetName))))
  /-
  Regardless of whether the `intros` succeeded, `False` means we are done with the conclusion.
  -/
  Tactic.withMainContext do
  if (←(←getMainGoal).getType) != q(False) then
    trace[EzPz.Tactic.ff.trace.target] "Γ ⊢ _ = _ → Γ, _ ≠ _ ⊢ False"
    evalTactic (←(`(tactic|by_contra! target)))

def processInequalities : TacticM Unit := Tactic.withMainContext do
  let ineqs ← liftM <| (← zModIneqs (←getMainGoal)).mapM fun f ↦ return mkIdent (← FVarId.getUserName f)
  trace[EzPz.Tactic.ff.trace.ineqs] "{ineqs} in\n {←getMainGoal}"
  discard <| ineqs.mapM eqOfNeq

end

elab "FF" : tactic => do
  withTraceNode `EzPz.Tactic.ff.trace (return m!"{exceptEmoji ·} Negate conclusion.") do
    tryNegateConclusion
  withTraceNode `EzPz.Tactic.ff.trace (return m!"{exceptEmoji ·} Eliminate inequalities.") do
    processInequalities
  let cocoa ← cocoaOfCVC5 (←Tactic.getMainGoal)
  finiteFieldCVC.toTacticM cocoa

end EzPz
