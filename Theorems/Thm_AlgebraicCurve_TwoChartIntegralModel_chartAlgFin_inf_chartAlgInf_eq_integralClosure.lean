import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_chartAlgFin_inf_chartAlgInf_eq_integralClosure

set_option autoImplicit false

universe u

open AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.chartAlgFin_inf_chartAlgInf_eq_integralClosure
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    (chartAlgFin R F j) ⊓ (chartAlgInf R F j) = integralClosure R F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_chartAlgFin_inf_chartAlgInf_eq_integralClosure.solution
