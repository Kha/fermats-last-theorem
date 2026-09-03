import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois
    {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
    (O₁ O₂ : ValuationSubring F)
    (h : ∀ x : E, algebraMap E F x ∈ O₁ ↔ algebraMap E F x ∈ O₂) :
    ∃ σ : F ≃ₐ[E] F, σ • O₁ = O₂ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois.solution
