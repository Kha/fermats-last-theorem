import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_range_eq_range_aeval_X_of_isIntegral_adjoin_singleton
set_option autoImplicit false
universe u v
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgHom.range_eq_range_aeval_X_of_isIntegral_adjoin_singleton
    (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B] (b₀ : B)
    (hint : ∀ b : B, IsIntegral ↥(Algebra.adjoin k ({b₀} : Set B)) b)
    (ψ : B →ₐ[k] RatFunc k) (hψ : ψ b₀ = RatFunc.X) :
    ψ.range = (Polynomial.aeval (RatFunc.X : RatFunc k)).range := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_range_eq_range_aeval_X_of_isIntegral_adjoin_singleton.solution
