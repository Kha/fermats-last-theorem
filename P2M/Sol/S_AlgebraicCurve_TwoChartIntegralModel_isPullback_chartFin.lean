import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isPullback_chartFin

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R'] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j})))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R' (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R' F j))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  letI : Algebra (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j})
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j}) :=
    (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j}).toAlgebra
  haveI : IsScalarTower R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j})
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j}) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j}) M)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j}) :=
    AlgebraicCurve.TwoChartIntegralModel.isLocalization_chartAlg R F R' M {j}
  haveI : Algebra.IsPushout R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j}) R'
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j}) :=
    Algebra.isPushout_of_isLocalization M R' _ _
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {j}) R'
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F {j}))
