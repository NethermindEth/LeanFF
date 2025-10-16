import Lean
import Qq

import FF.CoCoA

open Lean Elab Term Qq

namespace EzPz

namespace CoCoA

declare_syntax_cat cocoa
declare_syntax_cat reduction
declare_syntax_cat polynomial
declare_syntax_cat zmodeq

abbrev Cocoa := TSyntax `cocoa
abbrev Reduction := TSyntax `reduction
abbrev Polynomial := TSyntax `polynomial
abbrev ZmodEq := TSyntax `zmodeq

syntax "UNSAT" "(" "ORDER" "(" ident,* ")" "REDUCTIONS" "(" reduction* ")" "POLYNOMIALS" "(" polynomial* ")" ")" : cocoa

syntax indexedTerm := num noWs "{" zmodeq "}"

syntax "P(" num "," zmodeq ")" : polynomial
syntax "PN(" num "," zmodeq "," ident ")" : polynomial

syntax "M(" num "," num ")" : reduction
syntax "S(" indexedTerm "," indexedTerm "," num ")" : reduction
syntax "R(" num ";" indexedTerm,* ";" num ")" : reduction

syntax num : zmodeq
syntax ident : zmodeq
syntax "-" num : zmodeq
syntax "-" zmodeq : zmodeq
syntax "diseq" "[" num "]" : zmodeq
syntax zmodeq " * " zmodeq : zmodeq
syntax zmodeq " + " zmodeq : zmodeq
syntax zmodeq " - " zmodeq : zmodeq
syntax ident "^" num : zmodeq

syntax "[zmodeq|" zmodeq "]" : term
syntax "[CoCoA|" cocoa "]" : term

/--
For one reason or the other, CoCoA shapeshifts identifiers containing underscores from `a_b` to `a__b`,
and in general, from `a_ᵏb` to `a_²ᵏb`.

We reverse this change here.
-/
def originalIdentOfCocoaIdent (ident : String) : String :=
  ⟨(ident.data.splitBy fun x₁ x₂ ↦ x₁ == '_' && x₂ == '_').flatMap fun l ↦
     if l.head? == .some '_' then l.take (l.length / 2) else l⟩

def translateIdent (idn : TSyntax `ident) : MacroM StrLit :=
  pure (Syntax.mkStrLit <| originalIdentOfCocoaIdent idn.getId.toString)

private partial def translateZmodEq : ZmodEq → MacroM String
  | `(zmodeq|$n:num) =>
    pure s!"{n.getNat}"
  | `(zmodeq|$idn:ident) => do
    let idn ← translateIdent idn
    pure idn.getString
  | `(zmodeq|-$n:num) =>
    pure s!"-{n.getNat}"
  | `(zmodeq|diseq[$_]) =>
    pure "ineq"
  | `(zmodeq|-$n:zmodeq) => do
    pure s!"-{← translateZmodEq n}"
  | `(zmodeq|$lhs * $rhs) => do
    let lhs ← translateZmodEq lhs
    let rhs ← translateZmodEq rhs
    pure s!"{lhs} * {rhs}"
  | `(zmodeq|$lhs + $rhs) => do
    let lhs ← translateZmodEq lhs
    let rhs ← translateZmodEq rhs
    pure s!"{lhs} + {rhs}"
  | `(zmodeq|$lhs - $rhs) => do
    let lhs ← translateZmodEq lhs
    let rhs ← translateZmodEq rhs
    pure s!"{lhs} - {rhs}"
  | `(zmodeq|$lhs:ident ^ $rhs:num) => do
    let idn ← translateIdent lhs
    pure s!"{idn.getString} ^ {rhs.getNat}"
  | stx => Macro.throwError s!"Unrecognised: {stx}"

macro_rules
  | `([zmodeq|$z]) => do pure (Syntax.mkStrLit (← translateZmodEq z))

macro_rules
  | `(indexedTerm|$n{$t}) => do let t ← translateZmodEq t
                                let t := Syntax.mkStrLit t
                                `(Ast.IndexedTerm.mk $n $t)

open Ast Polynomial Reduction

def translateIndexedTerm : TSyntax `EzPz.CoCoA.indexedTerm → MacroM Term
  | `(indexedTerm|$n{$t}) => do let t ← translateZmodEq t
                                let t := Syntax.mkStrLit t
                                `(Ast.IndexedTerm.mk $n $t)
  | stx => Macro.throwError s!"Expected IndexedTerm. Got: {stx}"

def translateReduction : Reduction → MacroM Term
  | `(reduction|M($n₁, $n₂)) => `(M $n₁ $n₂)
  | `(reduction|S($i₁{$t₁}, $i₂{$t₂}, $n)) => do
    let t₁ ← translateZmodEq t₁
    let t₁ := Syntax.mkStrLit t₁
    let t₂ ← translateZmodEq t₂
    let t₂ := Syntax.mkStrLit t₂
    `(S ⟨$i₁, $t₁⟩ ⟨$i₂, $t₂⟩ $n)
  | `(reduction|R($n₁; $[$its],*; $n₂)) => do
    let indexedTerms ← its.mapM translateIndexedTerm
    `(R $n₁ $n₂ #[$indexedTerms,*])
  | stx => Macro.throwError s!"Expected Reduction. Got: {stx}"

def translatePolynomial : Polynomial → MacroM Term
  | `(polynomial|P($n, $t)) => do
    let t ← translateZmodEq t
    let t := Syntax.mkStrLit t
    `(P $n $t .none)
  | `(polynomial|PN($n, $t, $name)) => do
    let t ← translateZmodEq t
    let t := Syntax.mkStrLit t
    let name ← translateIdent name
    `(P $n $t (.some (Name.mkSimple $name)))
  | stx => Macro.throwError s!"Unrecognised: {stx}"

def translateCocoa : Cocoa → MacroM Term
  | `(cocoa|UNSAT(ORDER($[$indets],*) REDUCTIONS($[$reductions]*) POLYNOMIALS($[$polynomials]*))) => do
    let indets ← indets.mapM translateIdent
    let reductions ← reductions.mapM translateReduction
    let polynomials ← polynomials.mapM translatePolynomial
    `(Ast.Cocoa.mk #[$reductions,*] #[$polynomials,*] #[$indets,*])
  | stx => Macro.throwError s!"Expected Cocoa. Got: {stx}"

macro_rules
  | `([CoCoA|$cocoa]) => translateCocoa cocoa

end CoCoA

end EzPz
