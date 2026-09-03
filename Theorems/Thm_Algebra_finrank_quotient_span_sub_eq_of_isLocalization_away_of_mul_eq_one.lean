import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one

universe u

open Polynomial

theorem Algebra.finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one
    {K : Type u} [Field K] {D E O : Type u} [CommRing D] [CommRing E] [CommRing O]
    [IsDomain D] [IsDomain E] [Algebra K D] [Algebra K E] [Algebra K O]
    (φ : D →ₐ[K] O) (ψ : E →ₐ[K] O) (a : D) (b : E)
    (hφ : letI := φ.toRingHom.toAlgebra; IsLocalization.Away a O)
    (hψ : letI := ψ.toRingHom.toAlgebra; IsLocalization.Away b O)
    (hab : φ a * ψ b = 1)
    (hfinD : (Polynomial.aeval a : K[X] →ₐ[K] D).toRingHom.Finite)
    (hfinE : (Polynomial.aeval b : K[X] →ₐ[K] E).toRingHom.Finite)
    (hinj : Function.Injective (Polynomial.aeval a : K[X] →ₐ[K] D))
    (x : K) :
    Module.finrank K (D ⧸ Ideal.span {a - algebraMap K D x}) =
      Module.finrank K (E ⧸ Ideal.span {b}) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one.solution
