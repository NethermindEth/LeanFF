import Mathlib.Data.ZMod.Basic

namespace EzPz

namespace CoCoA

namespace Ast

open Lean

structure IndexedTerm where
  i : ℕ
  t : String
  deriving Inhabited, Repr, BEq, Hashable

inductive Reduction where
  | M (i₁ i₂ : ℕ)
  | S (t₁ t₂ : IndexedTerm) (i : ℕ)
  | R (i₁ i₂ : ℕ) (l : Array IndexedTerm)
  deriving Inhabited, Repr, BEq, Hashable

def Reduction.source : Reduction → ℕ
  | M i₁ _ => i₁
  | S {i := i, ..} _ _ => i
  | R i₁ _ _ => i₁

def Reduction.target : Reduction → ℕ
  | M _ i₂ => i₂
  | S _ _ i => i
  | R _ i₂ _ => i₂

def Reduction.dependencies (reduction : Reduction) : Array ℕ :=
  match reduction with
  | .M .. => #[reduction.source]
  | .S _ ⟨n, _⟩ _ => #[reduction.source] ++ #[n]
  | .R src _ terms => #[src] ++ terms.map IndexedTerm.i

def Reduction.simpleName : Reduction → Name
  | .M .. => `M
  | .S .. => `S
  | .R .. => `R

structure Polynomial where
  P :: i : ℕ
       t : String
       name : Option Name
  deriving Inhabited, Repr

structure Cocoa where
  reductions : Array Reduction
  polynomials : Array Polynomial
  indetsOrder : Array String
  deriving Inhabited, Repr

def Cocoa.reductionOfTarget (target : ℕ) (cocoa : Cocoa) : Option Reduction :=
  cocoa.reductions.find? (·.target == target)

def Cocoa.polynomialOfIdx (idx : ℕ) (cocoa : Cocoa) : Option String :=
  Polynomial.t <$> cocoa.polynomials.find? (·.i == idx)

end Ast

end CoCoA

end EzPz
