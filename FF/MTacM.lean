import Mathlib.Data.Nat.Basic
import Std.Data.TreeMap
import Lean
import FF.CoCoA

namespace EzPz

open Lean CoCoA Ast

structure SyncMap where
  st : Std.HashMap ℕ Name
  seen : Std.HashSet Reduction
  deriving Repr, Inhabited

def SyncMap.union (l r : SyncMap) : SyncMap :=
  {
    st := l.st.union r.st
    seen := l.seen.union r.seen
  }

def SyncMap.visit (node : Reduction) (m : SyncMap) : SyncMap :=
  {m with seen := m.seen.insert node}

def SyncMap.associate (idx : ℕ) (name : Name) (m : SyncMap) : SyncMap :=
  {m with st := m.st.insert idx name}

def SyncMap.identOfIdx (idx : ℕ) (m : SyncMap) : Ident :=
  mkIdent m.st[idx]!

structure NormaliseST where
  goal : MVarId
  goals : Array MVarId
  cocoa : Ast.Cocoa

def NormaliseST.indets (st : NormaliseST) : Array String := st.cocoa.indetsOrder

/--
Similar to `TacticM`.
-/
abbrev MTacM := StateT NormaliseST Elab.Tactic.TacticM

def Polynomial.toStx (p : Polynomial) : MTacM (Term × Term) := do
  match Parser.runParserCategory (←getEnv) `term p.t with
  | .ok stx => let stx : Term := ⟨stx⟩
               let i : Term := Syntax.mkNatLit p.i
               pure (i, stx)
  | .error e => throwError s!"Cannot parse {repr p};\nInner error: {e}"

def CoCoA.Ast.IndexedTerm.toStx (it : IndexedTerm) : MTacM (Term × Term) :=
  Polynomial.toStx ⟨it.1, it.2, .none⟩

abbrev Location := TSyntax `Lean.Parser.Tactic.location

end EzPz

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace.target (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace.ineqs (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace.smt (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace.initPolies (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace.reduction (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace.reduction.R (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace.reduction.S (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.trace.reduction.M (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.smt (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.resultHyp (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.normalise (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.normalise.lc (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.normalise.constants (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.normalise.clamp (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.reduction (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.reduction.R (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.reduction.S (inherited := true)

initialize Lean.registerTraceClass `EzPz.Tactic.ff.debug.reduction.M (inherited := true)

register_option EzPz.cvc5cmd : String := {
  defValue := "cvc5"
  group := "FF"
  descr := "cvc5 in your local environment (TODO: Our modified version. What do we type here.)"
}

register_option EzPz.cvc5lib : String := {
  defValue := "/usr/local/lib"
  group := "FF"
  descr := "LD_LIBRARY_PATH"
}
