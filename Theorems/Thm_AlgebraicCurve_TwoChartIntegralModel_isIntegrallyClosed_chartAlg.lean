import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

universe u
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (S : Set F) :
    IsIntegrallyClosed ↥(chartAlg R F S) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg.solution
