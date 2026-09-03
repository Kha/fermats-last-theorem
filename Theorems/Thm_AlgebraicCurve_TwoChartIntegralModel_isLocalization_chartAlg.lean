import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.isLocalization_chartAlg
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R'] (S : Set F) :
    letI : Algebra (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)
        (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F S) :=
      (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S).toAlgebra
    IsLocalization (M.map (algebraMap R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)))
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F S) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg.solution
