import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq

set_option autoImplicit false

universe u

theorem ValuationSubring.mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq
    {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (K' : IntermediateField K Ω)
    (τ : Ω ≃ₐ[K] Ω)
    (hτ : ∀ x : Ω,
      x ∈ IntermediateField.fixedField (A.decompositionSubgroup K ⊓ K'.fixingSubgroup) ⊓
        (separableClosure ↥K' Ω).restrictScalars K →
      τ x = x) :
    τ ∈ A.decompositionSubgroup K := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq.solution
