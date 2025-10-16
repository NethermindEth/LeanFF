import Lean

import FF.MTacM
import FF.Normalise

namespace EzPz

open Lean

lemma ne_zero_iff {n : ℕ} {x : ZMod n} [Fact (Nat.Prime n)] : x ≠ 0 ↔ ∃ v, v * x - 1 = 0 := by
  refine ⟨fun h ↦ ?p₁, fun h ↦ ?p₂⟩
  · use x⁻¹
    rw [inv_mul_cancel₀ h]
    grind
  · aesop

set_option hygiene false in
open Elab Tactic in
/--
Write `x ≠ 0` as `v * x - 1 = 0` for some `v`. This ensures we only reason about equalities.
-/
def eqOfNeq (loc : Ident) : TacticM Unit := Tactic.withMainContext do
  let freshName ← Tactic.withMainContext (Meta.getUnusedUserName `ineq)
  let freshName : Ident := mkIdent freshName
  evalTactic (←(
    `(tactic|(rw [ne_zero_iff] at $loc:ident
              rcases $loc:ident with ⟨$loc, $freshName⟩)))
  )

end EzPz
