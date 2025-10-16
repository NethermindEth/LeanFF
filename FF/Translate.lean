import Mathlib.Data.ZMod.Basic
import Qq
import Lean
import Lean.Data.NameMap
import FF.Normalise
import FF.MTacM

open Qq Lean

namespace EzPz

def translateNary (op : String) (args : List String) : String :=
  s!"({op} {String.join <| args.intersperse " "})"

partial def translate {k : Q(ℕ)} (e : Q(ZMod $k)) : MetaM String := do
  match e with
  | ~q(@OfNat.ofNat (ZMod _) $nQ $_instQ) =>
    return s!"(as ff{nQ.natLit!} FF{← unsafe Meta.evalExpr ℕ q(ℕ) k})"
  | ~q($xQ + $yQ) =>
    return translateNary "ff.add" [←translate xQ, ←translate yQ]
  | ~q($xQ * $yQ) =>
    return translateNary "ff.mul" [←translate xQ, ←translate yQ]
  | ~q($xQ - $yQ) =>
    translate q($xQ + (-$yQ))
  | ~q(-$xQ) =>
    return translateNary "ff.neg" [←translate xQ]
  | ~q($xQ ^ $yQ) =>
    return translateNary "ff.mul" <| List.replicate (← unsafe Meta.evalExpr ℕ q(ℕ) yQ) (←translate xQ)
  | ~q($e) => let some n := e.fvarId? | throwError "Cannot translate: {e}"
              return (←n.getUserName).toString

def translateEq (eQ : Q(Prop)) : MetaM String := do
  match eQ with
  | ~q(@Eq (ZMod $k) $xQ $yQ) => return translateNary "=" [←translate xQ, ←translate yQ]
  | _ => throwError m!"{eQ} is not a ZMod equation."

def translateHypname (x : Option FVarId) : MetaM Name :=
  match x with | .none => return Name.mkSimple "goal" | .some x => x.getUserName >>= pure

open Lean Parser Expr Elab Tactic in
def extractSmtLib (goal : MVarId) : MetaM String := do
  let .some (indets, mod) ← consistentIndeterminates goal | throwError "Cannot extract the goal."
  let mut result := "(set-logic QF_FF)"
  result := result.append "\n" |>.append s!"(define-sort FF{mod} () (_ FiniteField {mod}))"
  for name in indets do
    result := result.append "\n" |>.append s! "(declare-fun {name} () FF{mod})"
  for (name, expr) in ←exprMap (←`(location|at *)) goal do
    result := result.append "\n" |>.append s!"(assert (! {←translateEq expr} :named {←translateHypname name}))"
  return result

end EzPz
