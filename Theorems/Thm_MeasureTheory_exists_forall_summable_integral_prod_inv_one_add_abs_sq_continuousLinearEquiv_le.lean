import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le
    (a b r : ℕ) (S : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] (Fin r → ℝ)) :
    ∃ K : ℝ, ∀ (ψ : Fin a → ℝ) (t : Fin r → ℝ),
      (∀ κ : Fin a → ℤ, Integrable fun η : Fin b → ℝ =>
        ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2) ∧
      Summable (fun κ : Fin a → ℤ =>
        ∫ η : Fin b → ℝ, ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2) ∧
      ∑' κ : Fin a → ℤ, ∫ η : Fin b → ℝ, ∏ i, (1 + |S ((fun j => (κ j : ℝ) + ψ j), η) i - t i|)⁻¹ ^ 2 ≤ K := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_summable_integral_prod_inv_one_add_abs_sq_continuousLinearEquiv_le.solution
