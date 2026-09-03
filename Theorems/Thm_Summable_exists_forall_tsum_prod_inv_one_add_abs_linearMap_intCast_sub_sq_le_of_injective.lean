import Mathlib
import P2M.Util
import P2M.Sol.S_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective

set_option autoImplicit false

theorem Summable.exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective
    (a r : ℕ) (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (hA : Function.Injective A) :
    ∃ K : ℝ, ∀ t : Fin r → ℝ,
      Summable (fun k : Fin a → ℤ => ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2) ∧
      ∑' k : Fin a → ℤ, ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2 ≤ K := by p2m_exact_reverting @_root_.P2MW.S_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective.solution
