import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer
    (Γ : Subgroup SL(2, ℤ)) (τ : UpperHalfPlane) :
    Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) *
        Nat.card (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) =
      2 * Nat.card (MulAction.stabilizer Γ τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer.solution
