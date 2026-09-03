import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    Smooth (TwoChartIntegralModel.toBase R F j) ↔
      Algebra.Smooth R ↥(TwoChartIntegralModel.chartAlgFin R F j) ∧
        Algebra.Smooth R ↥(TwoChartIntegralModel.chartAlgInf R F j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf.solution
