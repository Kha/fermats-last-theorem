import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isPullback_chartInf

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.isPullback_chartInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R'] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j⁻¹})))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R' (AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R' F j))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isPullback_chartInf.solution
