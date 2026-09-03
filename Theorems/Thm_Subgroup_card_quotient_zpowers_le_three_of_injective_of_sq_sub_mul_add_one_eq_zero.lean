import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero

set_option autoImplicit false

theorem Subgroup.card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero
    (M : ℕ) (hM : 3 ≤ M) (H : Type*) [CommGroup H] [Finite H]
    (c : H) (hc2 : c * c = 1)
    (χ : H →* (ZMod M)ˣ) (hχ : Function.Injective χ) (hc : ((χ c : (ZMod M)ˣ) : ZMod M) = -1)
    (htr : ∀ h : H, ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      ((χ h : (ZMod M)ˣ) : ZMod M) ^ 2 - (t : ZMod M) * ((χ h : (ZMod M)ˣ) : ZMod M) + 1 = 0 ∧
      (t = 2 → h = 1) ∧ (t = -2 → h = c)) :
    Nat.card (H ⧸ Subgroup.zpowers c) ≤ 3 ∧ IsCyclic (H ⧸ Subgroup.zpowers c) ∧
      (2 ∣ Nat.card (H ⧸ Subgroup.zpowers c) → ∃ lam : ZMod M, lam ^ 2 + 1 = 0) ∧
      (3 ∣ Nat.card (H ⧸ Subgroup.zpowers c) → ∃ lam : ZMod M, lam ^ 2 + lam + 1 = 0) := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero.solution
