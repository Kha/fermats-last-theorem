import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem

set_option autoImplicit false

universe u v

theorem IntermediateField.finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem
    (K : Type u) [Field K] (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (S : Set Ω) (hS : S.Finite) (hsep : ∀ x ∈ S, IsSeparable K x)
    (hstab : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ S, σ x ∈ S) :
    FiniteDimensional K ↥(IntermediateField.adjoin K S) ∧ IsGalois K ↥(IntermediateField.adjoin K S) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem.solution
