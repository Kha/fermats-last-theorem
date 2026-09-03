import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite

set_option autoImplicit false

theorem ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois_infinite
    {E F : Type*} [Field E] [Field F] [Algebra E F] [IsGalois E F]
    (O : ValuationSubring E)
    (O' O'' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) :
    ∃ σ : F ≃ₐ[E] F, ∀ x : F, σ x ∈ O'' ↔ x ∈ O' := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite.solution
