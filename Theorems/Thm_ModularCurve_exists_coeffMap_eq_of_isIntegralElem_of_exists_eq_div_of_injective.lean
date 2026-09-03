import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
set_option autoImplicit false
open ModularCurve
theorem ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] (φ : R →+* K) (hφ : Function.Injective φ)
    (y : LaurentSeries K)
    (hy : ∃ a b : LaurentSeries R, b ≠ 0 ∧ y = coeffMap φ a / coeffMap φ b)
    (hint : (coeffMap φ).IsIntegralElem y) :
    ∃ c : LaurentSeries R, coeffMap φ c = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective.solution
