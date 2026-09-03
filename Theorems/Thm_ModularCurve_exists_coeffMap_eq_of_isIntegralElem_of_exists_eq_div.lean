import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div

theorem ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div (y : LaurentSeries ℚ)
    (hy : ∃ a b : LaurentSeries ℤ, b ≠ 0 ∧
      y = ModularCurve.coeffMap (Int.castRingHom ℚ) a / ModularCurve.coeffMap (Int.castRingHom ℚ) b)
    (hint : (ModularCurve.coeffMap (Int.castRingHom ℚ)).IsIntegralElem y) :
    ∃ c : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom ℚ) c = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div.solution
