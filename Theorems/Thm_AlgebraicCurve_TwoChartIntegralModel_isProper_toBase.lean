import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase

set_option autoImplicit false

universe u

open AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.isProper_toBase
    (R : Type u) [CommRing R] [IsNoetherianRing R] (F : Type u) [Field F] [Algebra R F]
    (j : F) [Fact (j ≠ 0)]
    [Algebra.FiniteType R ↥(chartAlgFin R F j)]
    [Algebra.FiniteType R ↥(chartAlgInf R F j)] :
    IsProper (toBase R F j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.solution
