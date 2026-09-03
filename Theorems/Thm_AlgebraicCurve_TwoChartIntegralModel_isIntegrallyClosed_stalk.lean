import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_stalk
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    IsIntegrallyClosed ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk.solution
