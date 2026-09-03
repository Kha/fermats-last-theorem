import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology

theorem AddSubgroup.exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology
    {r : ℕ} (Γ : AddSubgroup (Fin r → ℝ)) [DiscreteTopology Γ] :
    ∃ K : ℝ, ∀ (y : Fin r → ℝ) (F : Finset (Fin r → ℝ)), (↑F : Set (Fin r → ℝ)) ⊆ Γ →
      ∑ x ∈ F, ∏ k, (1 + |y k + x k|)⁻¹ ^ 2 ≤ K := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology.solution
