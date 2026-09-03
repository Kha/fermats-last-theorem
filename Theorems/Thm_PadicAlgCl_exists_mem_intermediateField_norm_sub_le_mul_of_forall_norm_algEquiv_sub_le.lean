import Mathlib
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le

set_option autoImplicit false

theorem PadicAlgCl.exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (δ : ℝ),
        (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
          ∃ a ∈ K, ‖α - a‖ ≤ c * δ := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le.solution
