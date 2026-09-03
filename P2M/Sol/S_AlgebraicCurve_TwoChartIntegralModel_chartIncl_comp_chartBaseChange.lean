import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_chartIncl_comp_chartBaseChange

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    {S S' : Set F} (h : S ⊆ S') :
    (AlgebraicCurve.TwoChartIntegralModel.chartIncl R' F h).toRingHom.comp
        (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S) =
      (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S').comp
        (AlgebraicCurve.TwoChartIntegralModel.chartIncl R F h).toRingHom := by
  refine RingHom.ext fun x => Subtype.ext ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl,
    AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange]
