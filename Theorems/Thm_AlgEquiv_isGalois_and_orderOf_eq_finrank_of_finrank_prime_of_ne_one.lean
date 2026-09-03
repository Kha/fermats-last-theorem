import Mathlib
import P2M.Util
import P2M.Sol.S_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one

set_option autoImplicit false

theorem AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    IsGalois K L ∧ orderOf σ = Module.finrank K L ∧ Subgroup.zpowers σ = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one.solution
