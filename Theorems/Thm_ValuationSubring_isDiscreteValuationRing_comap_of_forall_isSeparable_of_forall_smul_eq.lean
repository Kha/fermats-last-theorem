import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq

set_option autoImplicit false

universe u

theorem ValuationSubring.isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq
    {L : Type u} [Field L] {Ω : Type u} [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap L Ω)))
    (M : IntermediateField L Ω)
    (hsep : ∀ x : Ω, x ∈ M → IsSeparable L x)
    (hfix : ∀ σ : Ω ≃ₐ[L] Ω, σ ∈ A.decompositionSubgroup L → ∀ x : Ω, x ∈ M → σ x = x) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥M Ω)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq.solution
