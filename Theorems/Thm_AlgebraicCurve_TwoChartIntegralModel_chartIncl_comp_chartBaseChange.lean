import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_chartIncl_comp_chartBaseChange

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.chartIncl_comp_chartBaseChange
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    {S S' : Set F} (h : S ⊆ S') :
    (AlgebraicCurve.TwoChartIntegralModel.chartIncl R' F h).toRingHom.comp
        (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S) =
      (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S').comp
        (AlgebraicCurve.TwoChartIntegralModel.chartIncl R F h).toRingHom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_chartIncl_comp_chartBaseChange.solution
