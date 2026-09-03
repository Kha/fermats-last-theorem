import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Lifts
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegralElem_coeffMap_of_isIntegral_adjoin_jq

theorem ModularCurve.isIntegralElem_coeffMap_of_isIntegral_adjoin_jq (y : LaurentSeries ℚ)
    (hy : IsIntegral (Algebra.adjoin ℤ ({ModularCurve.jq} : Set (LaurentSeries ℚ))) y) :
    (ModularCurve.coeffMap (Int.castRingHom ℚ)).IsIntegralElem y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegralElem_coeffMap_of_isIntegral_adjoin_jq.solution
