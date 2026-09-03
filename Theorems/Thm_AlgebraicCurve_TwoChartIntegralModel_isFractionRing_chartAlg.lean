import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
set_option autoImplicit false
universe u
open AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg
    (R : Type u) [CommRing R] [IsDomain R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (S : Set F) [Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ S) F] :
    IsFractionRing ↥(chartAlg R F S) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg.solution
