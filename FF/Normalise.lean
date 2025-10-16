import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Basic
import Qq
import Lean
import FF.MTacM
import FF.CoCoA

open Lean Grind CommRing in
def Lean.Grind.CommRing.Poly.monomials (poly : Poly) : Array (Mon × ℤ) :=
  match poly with
  | .num k => #[(.unit, k)]
  | .add k v p => monomials p |>.push (v, k)

def Lean.Grind.CommRing.Mon.totalOrder (m : Mon) : ℕ :=
  match m with
  | .unit => 0
  | .mult p₁ mon₁ => p₁.x + mon₁.totalOrder

open Lean Grind CommRing in
def someOrder (x y : Mon) : Ordering :=
  match x, y with
  | .unit, .unit => .eq
  | .unit, .mult .. => .gt
  | .mult .., .unit => .lt
  | x, y => bif x.totalOrder < y.totalOrder then .gt
            else bif x.totalOrder = y.totalOrder then .eq
            else .lt

def Lean.Grind.CommRing.Mon.monCmp (x y : Mon) : Ordering :=
  compare x.degree y.degree |>.then (someOrder x y)

def Lean.Grind.CommRing.Power.pretty (p : Power) (indets : Std.TreeMap Var String) : String :=
  s!"{indets[p.x]!}^{p.k}"

def Lean.Grind.CommRing.Mon.pretty (m : Mon) (indets : Std.TreeMap Var String) : String :=
  match m with
  | .unit => ""
  | .mult p m => s!"{p.pretty indets}{if m matches .unit then "" else (" * " ++ m.pretty indets)}"

def Lean.Grind.CommRing.Poly.pretty (p : Poly) (indets : Std.TreeMap Var String) : String :=
  match p with
  | .num a => s!"{a}"
  | .add k m v => s!"{k} * {m.pretty indets} + {v.pretty indets}"

namespace EzPz

/--
Workaround to use a `term` parser instead of `location`.
-/
scoped syntax "spoon" Lean.Parser.Tactic.location : term

open Lean Qq Parser Elab Tactic Meta CoCoA

/--
Dumps `goal`'s context `FVarId → Name` assignments.

- Debugging only.
-/
private def debugGoalDecls (goal : Option MVarId) : MetaM Unit := do
  let m := logInfo m!"ctx: {repr (((←getLCtx).fvarIdToDecl).map (fun ldec ↦ ldec.userName)).toArray}"
  match goal with
  | .none => m
  | .some goal => goal.withContext m

/--
Dumps the main target.

- Debugging only.
-/
private def debugTarget (goal : MVarId) : MetaM Unit := goal.withContext do
  logInfo m!"target: {repr (←goal.getType)}"

def pOfZModEq (e : Expr) : MetaM (Option ℕ) := do
  let (``Eq, ⟨.app (.const name _) k :: _⟩) := e.getAppFnArgs | return .none
  let k ← unsafe evalExpr ℕ q(ℕ) k
  return if name == ``ZMod then .some k else .none

def isZModEq (e : Expr) : MetaM Bool :=
  pOfZModEq e <&> Option.isSome

def isZModIneq (e : Expr) : Bool := Id.run do
  let (``Ne, ⟨.app (.const name _) _ :: _⟩) := e.getAppFnArgs | return false
  return name == ``ZMod

/--
Contract: Systems are assumed to be of the form `Γ ⊢ False`.
-/
def zModEqs (goal : MVarId) : MetaM (Array FVarId) := goal.withContext do
  let Γmod ← (← getLocalHyps).filterM (inferType · >>= isZModEq)
  return Γmod.map (·.fvarId!)

/--
Contract: Systems are assumed to be of the form `Γ ⊢ False`.
-/
def zModIneqs (goal : MVarId) : MetaM (Array FVarId) := goal.withContext do
  let Γmod ← (← getLocalHyps).filterM (inferType · <&> isZModIneq)
  return Γmod.map (·.fvarId!)

def locationOfName (name : Name) : MetaM Location := do
  let .ok stx := runParserCategory (←getEnv) `term s!"spoon at {name}"
    | throwError s!"{name} cannot be used as location."
  let `(spoon $l:location) := stx | throwError "Malformed location."
  `(location| $l)

/--
Empty list of names means `at *`.
-/
def locationOfNames (names : Array Name) : MetaM Location := do
  let locationStr := s!"spoon at {" ".intercalate (names.map Name.toString).toList} " ++
                     s!"{if names.isEmpty then "*" else ""}"
  let .ok stx := runParserCategory (←getEnv) `term locationStr
    | throwError s!"{names} cannot be used as location."
  let `(spoon $l:location) := stx | throwError "Malformed location."
  `(location| $l)

def locationOfFVarId (goal : MVarId) (fv : FVarId) : MetaM Location := goal.withContext do
  locationOfNames #[←fv.getUserName]

def exprMapOfFVarIDsAndTarget (goal : MVarId)
                              (hyps : Array FVarId) : MetaM (Std.HashMap FVarId Expr) :=
  goal.withContext do
    let result := hyps.zip <| hyps.map (LocalDecl.type ∘ (← getLCtx).get!)
    return Std.HashMap.ofList result.toList

section

open Lean.Grind.CommRing

partial def grindMonoOfZMod {kQ : Q(ℕ)}
  (eQ : Q(ZMod $kQ)) (indetMap : Std.TreeMap String Var) : MetaM (Option Mon) := do
  let grindMonoOfZMod e := grindMonoOfZMod e indetMap
  match eQ with
  | ~q($xQ * $yQ) => do
    let .some x ← grindMonoOfZMod xQ | return .none
    let .some y ← grindMonoOfZMod yQ | return .none
    return .some (x.concat y)
  | ~q($xQ⁻¹ ^ $expQ) =>
    -- We match this explicitly to simplify the logic of `$indetQ ^ $expQ`.
    logError m!"Monomials must of the form `<indet>`, `<indet> * <indet>` or `<indet>^K`.\n{eQ} is impermissible."
    return .none
  | ~q($indetQ ^ $expQ) =>
    -- Qq is unhappy about matching on `indetQ` here.
    let .some name ← indetQ.fvarId?.mapM (·.getUserName) | throwError "Expected indet^n, got: {eQ}"
    return .some <| .mult ⟨indetMap[name.toString]!, ← unsafe evalExpr ℕ q(ℕ) expQ⟩ .unit
  | ~q(@OfNat.ofNat (ZMod _) $_nQ $_instQ) =>
    let n ← unsafe evalExpr (ZMod (← unsafe evalExpr ℕ q(ℕ) kQ)) q(ZMod $kQ) eQ
    if n != 1 then return .none
    return .some .unit
  | ~q($_symQ) => grindMonoOfZMod q($eQ^1)
  | _ => logError m!"Unrecognised ZMod eq shape: {eQ}."; return .none

partial def grindPolyOfZMod {kQ : Q(ℕ)}
  (eQ : Q(ZMod $kQ)) (indetMap : Std.TreeMap String Var) : MetaM (Option Poly) := do
  let .succ _ ← unsafe evalExpr ℕ q(ℕ) kQ | return .none
  let grindPolyOfZMod e := grindPolyOfZMod (kQ := kQ) e indetMap
  match eQ with
  | ~q($xQ + $yQ) =>
    let .some x ← grindPolyOfZMod xQ | return .none
    let .some y ← grindPolyOfZMod yQ | return .none
    return .some (x.combine y)
  | ~q($xQ - $yQ) =>
    let .some x ← grindPolyOfZMod xQ | return .none
    let .some y ← grindPolyOfZMod yQ | return .none
    return .some (x.combine (y.mulConst (-1)))
  | ~q((@OfNat.ofNat (ZMod _) $nQ $_instQ) * $monoQ) =>
    let n ← unsafe evalExpr ℕ q(ℕ) nQ
    let .some mon ← grindMonoOfZMod q($monoQ) indetMap | return .none
    return .some (Poly.num 0 |>.insert n.cast mon)
  | ~q(-(@OfNat.ofNat (ZMod _) $nQ $_instQ) * $monoQ) =>
    let n ← unsafe evalExpr ℕ q(ℕ) nQ
    let .some mon ← grindMonoOfZMod q($monoQ) indetMap | return .none
    return .some (Poly.num 0 |>.insert (-n.cast) mon)
  | ~q($monoQ * (@OfNat.ofNat (ZMod _) $nQ $_instQ)) =>
    -- Ouch, cannot do `name@pattern` in `~q()`.
    grindPolyOfZMod q((@OfNat.ofNat (ZMod _) $nQ $_instQ) * $monoQ)
  | ~q($monoQ * -(@OfNat.ofNat (ZMod _) $nQ $_instQ)) =>
    -- Ouch, cannot do `name@pattern` in `~q()`.
    grindPolyOfZMod q(-(@OfNat.ofNat (ZMod _) $nQ $_instQ) * $monoQ)
  | ~q(@OfNat.ofNat (ZMod _) $nQ $_instQ) =>
    grindPolyOfZMod q($eQ * 1)
  | ~q(@Neg.neg (ZMod _) $_instQ₁ (@OfNat.ofNat (ZMod _) $nQ $_instQ₂)) =>
    return .some (Poly.num (Int.negOfNat (← unsafe evalExpr ℕ q(ℕ) nQ)))
  | ~q(-$polyQ) =>
    Option.map (Poly.mulConst (-1)) <$> grindPolyOfZMod polyQ
  | ~q($monoQ) =>
    let .some mon ← grindMonoOfZMod monoQ indetMap | return .none
    return .some (Poly.ofMon mon)
  | _ => logError m!"Unrecognised ZMod eq shape: {eQ}."; return .none

def grindPolyOfZModEq (eQ : Q(Prop)) (indetMap : Std.TreeMap String ℕ) : MetaM (Option Poly) := do
  match eQ with
  | ~q(@Eq (ZMod $k) $lhs 0) => grindPolyOfZMod lhs indetMap
  | _ => throwError "Expected _ = 0. Got: {eQ}"

/--
In a polynomial `xc₁ * xc₂ * ... * xcₖ + xc₁' * xc₂' * ... * xcⱼ' + ... + xc₁'' * ... * xcₗ''`,
returns `[xcₖ, xcₖ', xcₗ'']`.
-/
partial def isolatedConstantsOfMonomials {kQ : Q(ℕ)} (eQ : Q(ZMod $kQ)) : MetaM (Array ℕ) := do
  let .succ _ ← unsafe evalExpr ℕ q(ℕ) kQ | return #[]
  match eQ with
  | ~q($xQ + $yQ) =>
    let x ← isolatedConstantsOfMonomials xQ
    let y ← isolatedConstantsOfMonomials yQ
    return x ++ y
  | ~q($xQ - $yQ) =>
    isolatedConstantsOfMonomials q($xQ + $yQ)
  | ~q(-$monoQ) =>
    isolatedConstantsOfMonomials q($monoQ)
  | ~q($monoQ) =>
    let ~q(_ * @OfNat.ofNat (ZMod _) $nQ $_instQ) := monoQ | return #[]
    return #[← unsafe evalExpr ℕ q(ℕ) nQ]

partial def constantOfMono {kQ : Q(ℕ)} (eQ : Q(ZMod $kQ)) : MetaM (Array ℤ) := do
  let .succ _ ← unsafe evalExpr ℕ q(ℕ) kQ | return #[]
  match eQ with
  | ~q($xQ * $yQ) =>
    let x ← constantOfMono xQ
    let y ← constantOfMono yQ
    return x ++ y
  | ~q(@OfNat.ofNat (ZMod _) $nQ $_instQ) =>
    return #[(← unsafe evalExpr ℕ q(ℕ) nQ)]
  | ~q(-@OfNat.ofNat (ZMod _) $nQ $_instQ) =>
    return #[-(← unsafe evalExpr ℕ q(ℕ) nQ)]
  | _ =>
    trace[EzPz.Tactic.ff.debug.normalise.constants] "{eQ} has no constants."
    return #[]

partial def constantsOfPoly {kQ : Q(ℕ)} (eQ : Q(ZMod $kQ)) : MetaM (Array ℤ) :=
  Array.sortDedup <$> do
  let .succ _ ← unsafe evalExpr ℕ q(ℕ) kQ | return #[]
  match eQ with
  | ~q($xQ + $yQ) =>
    let x ← constantsOfPoly xQ
    let y ← constantsOfPoly yQ
    return x ++ y
  | ~q($xQ - $yQ) =>
    constantsOfPoly q($xQ + $yQ)
  | ~q(-$polyQ) =>
    constantsOfPoly polyQ
  | ~q($monoQ) =>
    constantOfMono monoQ

end

abbrev MTac := MVarId → MetaM (List MVarId)

def NormaliseST.ofGoal (goal : MVarId) (cocoa : Ast.Cocoa) : NormaliseST :=
  {
    goal := goal
    goals := #[]
    cocoa := cocoa
  }

def MTacM.toTacticM {α : Type} [Inhabited α] (m : MTacM α) (cocoa : Ast.Cocoa) : TacticM α := do
  let goal :: goals ← getGoals | default
  let (r, st) ← m.run ⟨goal, goals.toArray, cocoa⟩
  setGoals (st.goal :: st.goals.toList)
  pure r

/--
Similar to `TacticM.withMainContext`.
-/
def withMainContext {α : Type} (m : MTacM α) : MTacM α := do (←get).goal.withContext m

/--
Evaluates to all `ZMod k` indeterminates of the system and enforces uniform `k`.
-/
def consistentIndeterminates (goal : MVarId) : MetaM (Option (Array String × ℕ)) := goal.withContext do
  let mut mod : Option Nat := .none
  let mut indets : Array String := #[]
  for hyp in ← getLocalHyps do
    let (``ZMod, #[(.app (.app _ kexpr@(.lit _)) _)]) := (←inferType hyp).getAppFnArgs | continue
    let k ← unsafe evalExpr ℕ q(ℕ) kexpr
    let name ← hyp.fvarId!.getUserName
    match mod with
    | .none => mod := .some k
               indets := indets.push name.toString
    | .some k' => if k == k'
                  then indets := indets.push name.toString
                  else return .none
  return pure (indets.qsort (· > ·), mod.getD 0)

def indeterminatesMap (goal : MVarId) : MetaM (Std.TreeMap String ℕ) := goal.withContext do
  let .some (indets, _) ← consistentIndeterminates goal | throwError "The system is inconsistent."
  return Std.TreeMap.ofList indets.zipIdx.toList

def systemMod (goal : MVarId) : MTacM ℕ := goal.withContext do
  let .some (_, mod) ← consistentIndeterminates goal | throwError "The system is inconsistent."
  return mod

/--
Lift a function of `MVarId` to operate over `MTacM` instead. The domain determines the main goal.
-/
def lift {α : Type} (f : MVarId → MetaM α) : MTacM α := do f (←get).goal

def liftMTac (f : MTac) : MTacM Unit := do
  match ← lift f with
  | [] => pure ()
  | goal :: goals => set {
      NormaliseST.ofGoal goal (←get).cocoa
        with goals := goals.toArray ++ (←get).goals
    }

def locationOfZModEqs : MTacM Location := do
  let zmodEqs ← lift zModEqs
  locationOfNames (←zmodEqs.mapM (·.getUserName))

instance : Ord FVarId where
  compare a b :=
    if a.name.toString < b.name.toString then .lt else
    if a.name == b.name then .eq else .gt

def exprMap (l : Location) (goal : MVarId) : MetaM (Std.TreeMap FVarId Expr) := goal.withContext do
  let hyps ←
    match expandLocation l with
    | .wildcard => zModEqs goal
    | .targets hyps conclusion =>
        if conclusion then logInfo "Requested the expression at conclusion; this is always `False`."
        let lctx ← getLCtx
        let hyps := hyps.map fun stx ↦
          lctx.findFromUserName? stx.getId |>.elim default (·.fvarId)
        pure hyps
  let result := hyps.zip <| hyps.map (LocalDecl.type ∘ (←getLCtx).get!)
  return Std.TreeMap.ofList result.toList

def debugHypsOfLoc (l : Location) : MTacM String := withMainContext do
  let mut result := ""
  for (hyp, e) in ← lift (exprMap l) do
    result := s!"{result}{←hyp.getUserName} : {←ppExpr (←instantiateMVars e)}"
  return result

def debugBracketHypOfLoc {α : Type} (l : Location) (cls : Name) (m : MTacM α) : MTacM α := withMainContext do
  if (← Lean.isTracingEnabledFor cls) then Lean.addTrace cls (←debugHypsOfLoc l)
  let res ← m
  withMainContext do
    if (← Lean.isTracingEnabledFor cls) then Lean.addTrace cls (←debugHypsOfLoc l)
  return res

def runTactic' (tacticCode : Syntax) (mvarId : MVarId) : MetaM (List MVarId) :=
  (·.1) <$> runTactic mvarId tacticCode

abbrev runTactic : Syntax → MTacM Unit := liftMTac ∘ runTactic'

abbrev runTacticInΓ : Syntax → MTacM Unit :=
  withMainContext ∘ runTactic

def normaliseConstant (mod : ℕ) (c : ℤ) : ℤ :=
  let c := c % mod
  if c ≤ (mod / 2)
  then c
  else - (mod - c)

def leadingCoeff_grevlex (e : Expr) : MTacM ℤ := do
  let .some grindPoly ← grindPolyOfZModEq e <| Std.TreeMap.ofList (←get).indets.zipIdx.toList
    | throwError "Failed to compute LC of: {e}"
  return grindPoly.lc

def leadingCoeff (e : Expr) : MTacM ℤ := do
  let indexedIndets := (←get).indets.zipIdx.toList
  /-
  We use Grind's polynmomial representation as a convenience IR.
  -/
  let .some grindPoly ← grindPolyOfZModEq e (Std.TreeMap.ofList indexedIndets)
    | throwError "Failed to compute LC of: {e}"
  /-
  It's easier to order the monomials this way, rather than at the `Expr` level.
  -/
  let ordered := grindPoly.monomials.qsort fun (m₁, _) (m₂, _) ↦ m₁.monCmp m₂ == .gt
  let lc := ordered[0]?.elim 1 Prod.snd
  trace[EzPz.Tactic.ff.debug.normalise.lc]
    s!"Poly in order[LC={lc}]: {dbgPrettyMonos ordered indexedIndets}"
  return lc
  where
    dbgPrettyMonos (monos : Array (Grind.CommRing.Mon × ℤ))
                   (indexedIndets : List (String × ℕ)) : String :=
      String.join <|
        monos.map
          (fun (m, k) ↦
            if m matches .unit
            then s!"{k}"
            else s!"{k} * ({m.pretty (Std.TreeMap.ofList <| indexedIndets.map fun (a, b) ↦ (b, a))})")
        |>.toList.intersperse " + "

def overrideLocation (l : Location) : MTacM Location := withMainContext do
  if expandLocation l matches .wildcard then locationOfZModEqs else pure l

def ring_nf (l : Location) : MTacM Unit := withMainContext do
  let loc ← overrideLocation l
  runTactic (←`(tactic| try (ring_nf $loc:location)))

def clampToField (l : Location) : MTacM Unit := withMainContext do
  let mod ← systemMod (←get).goal
  let modQ : Q(ℕ) := toExpr mod
  let modStx := Syntax.mkNatLit mod
  for (_, e) in ← lift (exprMap l) do
    let_expr Eq _ lhs _ := e | continue
    let constants ← constantsOfPoly (kQ := q($modQ)) lhs
    trace[EzPz.Tactic.ff.debug.normalise.constants] "{e} constants: {constants}"
    for c in constants do
      let .ok cStx := Parser.runParserCategory (←getEnv) `term s!"{c}"
        | throwError s!"Cannot parse: {c}"
      let cStx : Term := ⟨cStx⟩
      let cNormalised := normaliseConstant mod c
      if c == cNormalised then continue -- In ℤ, not in [MOD mod].
      let .ok cNormalisedStx :=
        Parser.runParserCategory (←getEnv) `term s!"{cNormalised}"
        | throwError s!"Cannot parse: {cNormalised}"
      let cNormalisedStx : Term := ⟨cNormalisedStx⟩
      trace[EzPz.Tactic.ff.debug.normalise.clamp] "Changing {cStx} to {cNormalisedStx}"
      runTacticInΓ (←`(tactic|try rw [show ($cStx : ZMod $modStx) = $cNormalisedStx by grind] $l))

def subst_eqs : MTacM Unit := withMainContext do
  runTactic (←`(tactic| subst_eqs))

def clamp (a : ℤ) (mod : ℕ) : ℕ := ((a.cast : ZMod mod).cast : ℤ).toNat

/--
Divides all ZMod equations by the leading coefficient. Discharges all necessary injectivity
obligations.
-/
def divideByLC (l : Location) : MTacM (Std.HashMap Name (ℤ × ℕ)) := withMainContext do
  let env ← getEnv
  let mod ← systemMod (←get).goal
  let modS := Syntax.mkNumLit s!"{mod}"
  let mut lcInfo : Std.HashMap Name (ℤ × ℕ) := {}
  for (hyp, e) in ← lift (exprMap l) do
    let lcZ ← leadingCoeff e
    let lc : ℕ := clamp lcZ mod
    let (_, inverse) := Nat.xgcd (←systemMod (←get).goal) lc
    lcInfo := lcInfo.insert (←hyp.getUserName) (lcZ, clamp inverse mod)
    let .ok lcZStx := runParserCategory env `term s!"{lcZ}" | throwError s!"{lcZ} is not a valid number."
    let lcZStx : Term := ⟨lcZStx⟩
    let loc ← locationOfNames #[←hyp.getUserName]
    let goals ← runTactic' (←`(tactic|apply_fun (·/($lcZStx : ZMod $modS)) $loc:location)) (←get).goal
    match goals with
    | [goal] => modify ({· with goal := ← liftM (goal.modifyTarget instantiateMVars)})
    | [goal, injective] =>
      modify ({· with goal := ← liftM (goal.modifyTarget instantiateMVars)})
      try let [] ← runTactic' (←`(tactic|(intros x y h
                                          try simp at h
                                          try rwa [div_left_inj'] at h
                                          grind)))
                              injective
                     | throwError "Discharging tactic didn't solve all goals."
      catch e => throwError m!"Cannot solve: {injective}\nWhy:\n{e.toMessageData}"
    | _ => throwError m!"Did not expect {goals.length} goals after `apply_fun`."
  return lcInfo

lemma neg_inv_mul_cancel₀ {α : Type*} [Field α] {x : α} (h : x ≠ 0)
  : (-x)⁻¹ * x = -1 := by simp only [inv_neg, neg_mul, neg_inj]; exact inv_mul_cancel₀ h

/--
Discharge `-C = C'` finite field equalities that are not `rfl`.
-/
local elab "neg_inv_mul_cancel" : tactic => do
  evalTactic (←`(tactic|(unfold_projs
                         simp [ZMod.inv, ZMod.val, ZMod, Nat.gcdA, Nat.xgcd, Nat.xgcdAux]
                         try rfl)))

/--
Normalisation after division by the leading coefficient. Cancels `a⁻¹ * a` and `-a⁻¹ * a`.
-/
def cancelMultiplicands (l : Location) (lcInfo : Std.HashMap Name (ℤ × ℕ)) : MTacM Unit := withMainContext do
  for (hyp, e) in ← lift (exprMap l) do
    have e : Q(Prop) := e
    let ~q(@Eq (ZMod $k) $lhs 0) := e | throwError s!"{e} must have rhs = 0."
    let res ← isolatedConstantsOfMonomials (kQ := q($k)) lhs
    if res.isEmpty then continue
    let hyp ← hyp.getUserName
    let mkRewriteFrom (lem loc : String) : String := s!"try rw [{lem}] at {loc}"
    let (lc, _) := lcInfo[hyp]!
    let rewrites :=
      "(\n" ++
      (
        (res.map (fun n ↦ mkRewriteFrom s!"@mul_assoc _ _ _ ({lc})⁻¹ {n}" s!"{hyp}") ++
         #[
           mkRewriteFrom "inv_mul_cancel₀ (by grind)" s!"{hyp}",
           mkRewriteFrom "mul_one" s!"{hyp}",
           mkRewriteFrom "neg_inv_mul_cancel₀ (by grind)" s!"{hyp}",
           mkRewriteFrom "mul_neg_one" s!"{hyp}"
         ]) |>.toList.intersperse "\n"
      ).foldl (·++·) "" ++
      "\n)"
    let .ok stx := runParserCategory (←getEnv) `tactic rewrites
      | throwError "{rewrites} is not a valid tactic."
    try
      runTactic stx
    catch e =>
      logInfo m!"Cannot cancel multiplicants. Inner error: {e.toMessageData}"

/--
Normalises inverses in a finite field.
-/
def normaliseConstants (lcInfo : Std.HashMap Name (ℤ × ℕ)) : MTacM Unit := withMainContext do
  let modS := Syntax.mkNatLit (←systemMod (←get).goal)
  let env ← getEnv
  for (name, const, inverse) in lcInfo do
    if inverse == 1 then continue
    let .ok const' :=
      runParserCategory env `term s!"{clamp const (←systemMod (←get).goal)}"
        | throwError s!"{const} is not a valid number."
    let const' : Term := ⟨const'⟩
    let inverse := Syntax.mkNatLit inverse
    let l ← locationOfNames #[name]
    let .ok const := runParserCategory env `term s!"{const}"
      | throwError s!"{const} is not a valid number."
    let const : Term := ⟨const⟩
    runTacticInΓ
      (←`(tactic|try rw [show ($const : ZMod $modS) = $const' by neg_inv_mul_cancel] $l:location))
    runTacticInΓ
      (←`(tactic|try rw [show (($const')⁻¹ : ZMod $modS) = $inverse from ZMod.inv_eq_of_mul_eq_one _ _ _ rfl] $l:location))

def clearRHS (l : Location) : MTacM Unit := withMainContext do
  let l ← overrideLocation l
  runTactic (←`(tactic| (repeat (try rw [←sub_eq_zero] $l))))  

/--
NB: Currently unused; unsurprisingly, `grind` continues to be faster than our custom normalise
strategy.

This should probably only live in source control :).
-/
def normaliseSystem (l : Location) : MTacM Unit := withMainContext do
  withTraceNode `EzPz.Tactic.ff.debug.normalise (return m!"{exceptEmoji ·} Normalise.") do
  ring_nf l
  clearRHS l
  clampToField l
  let lcInfo ← divideByLC l
  ring_nf l
  cancelMultiplicands l lcInfo -- Not necessary but seems to make the subsequent processing faster.
  normaliseConstants lcInfo
  ring_nf l

end EzPz
