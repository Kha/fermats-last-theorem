import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_baseChange_baseChange_of_isLocalization

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_iso_baseChange_baseChange_of_isLocalization
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R']
    (S : Type u) [CommRing S] [Algebra R S] [Algebra R' S] [IsScalarTower R R' S] :
    ∃ (u : AlgebraicCurve.TwoChartIntegralModel R' F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
      (e : AlgebraicCurve.TwoChartIntegralModel.baseChange R' F j S ≅
        AlgebraicCurve.TwoChartIntegralModel.baseChange R F j S),
      AlgebraicCurve.TwoChartIntegralModel.ιFin R' F j ≫ u =
        Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιFin R F j ∧
      AlgebraicCurve.TwoChartIntegralModel.ιInf R' F j ≫ u =
        Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j⁻¹})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιInf R F j ∧
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.baseChangeToBase R F j S =
        AlgebraicCurve.TwoChartIntegralModel.baseChangeToBase R' F j S ∧
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.baseChangeι R F j S =
        AlgebraicCurve.TwoChartIntegralModel.baseChangeι R' F j S ≫ u := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_baseChange_baseChange_of_isLocalization.solution
