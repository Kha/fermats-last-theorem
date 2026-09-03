import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField

set_option autoImplicit false

theorem ValuationSubring.mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (P : ValuationSubring L) (τ : L ≃ₐ[K] L)
    (h : ∀ x : L, x ∈ P → x ∈ IntermediateField.fixedField (P.decompositionSubgroup K) → τ x = x) :
    τ ∈ P.decompositionSubgroup K := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField.solution
