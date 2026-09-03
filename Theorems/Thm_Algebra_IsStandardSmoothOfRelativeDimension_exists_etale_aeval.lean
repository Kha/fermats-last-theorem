import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsStandardSmoothOfRelativeDimension_exists_etale_aeval

set_option autoImplicit false

universe u v

theorem Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_aeval
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ x : Fin n → S,
      (MvPolynomial.aeval x : MvPolynomial (Fin n) R →ₐ[R] S).toRingHom.Etale := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_exists_etale_aeval.solution
