import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_eq_of_comap_eq_of_forall_mem_decompositionSubgroup

set_option autoImplicit false

universe u

theorem ValuationSubring.eq_of_comap_eq_of_forall_mem_decompositionSubgroup
    {L : Type u} [Field L] {Ω : Type u} [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω)
    (hdec : ∀ σ : Ω ≃ₐ[L] Ω, σ ∈ A.decompositionSubgroup L)
    (B : ValuationSubring Ω) (hB : B.comap (algebraMap L Ω) = A.comap (algebraMap L Ω)) :
    B = A := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_eq_of_comap_eq_of_forall_mem_decompositionSubgroup.solution
