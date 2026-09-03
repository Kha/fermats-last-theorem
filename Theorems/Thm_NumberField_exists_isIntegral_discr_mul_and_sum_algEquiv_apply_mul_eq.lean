import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq

set_option autoImplicit false

theorem NumberField.exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ j, IsIntegral ℤ (a j)) ∧ (∀ j, IsIntegral ℤ ((NumberField.discr K : K) * b j)) ∧
      (∀ γ : K ≃ₐ[ℚ] K, ∑ j, γ (a j) * γ (b j) = 1) ∧
      ∀ γ δ : K ≃ₐ[ℚ] K, γ ≠ δ → ∑ j, γ (a j) * δ (b j) = 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq.solution
