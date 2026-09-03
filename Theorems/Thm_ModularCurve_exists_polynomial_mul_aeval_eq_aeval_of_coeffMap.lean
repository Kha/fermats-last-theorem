import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_polynomial_mul_aeval_eq_aeval_of_coeffMap
    {K₀ k : Type*} [Field K₀] [Field k] (ι : K₀ →+* k)
    (t r : LaurentSeries K₀) (ht : Transcendental K₀ t)
    (hr : ∃ P Q : Polynomial k, Polynomial.aeval (coeffMap ι t) Q ≠ 0 ∧
      coeffMap ι r * Polynomial.aeval (coeffMap ι t) Q = Polynomial.aeval (coeffMap ι t) P) :
    ∃ P Q : Polynomial K₀, Q ≠ 0 ∧ r * Polynomial.aeval t Q = Polynomial.aeval t P := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap.solution
