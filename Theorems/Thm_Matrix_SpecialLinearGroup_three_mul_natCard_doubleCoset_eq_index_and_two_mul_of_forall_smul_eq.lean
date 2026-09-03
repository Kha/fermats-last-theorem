import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hfree : ∀ γ : SL(2, ℤ), (γ ∈ Γ ∨ -γ ∈ Γ) → ∀ τ : UpperHalfPlane, γ • τ = τ → γ = 1 ∨ γ = -1) :
    3 * Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) =
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      2 * Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
          (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) =
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq.solution
