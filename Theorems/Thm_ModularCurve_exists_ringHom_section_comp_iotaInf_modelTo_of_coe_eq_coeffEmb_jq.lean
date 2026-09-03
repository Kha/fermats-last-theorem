import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringHom_section_comp_iotaInf_modelTo_of_coe_eq_coeffEmb_jq
attribute [-instance] AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin
attribute [-simp] AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.jqNModC_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.exists_ringHom_section_comp_iotaInf_modelTo_of_coe_eq_coeffEmb_jq
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ (ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A)
      (ε : Spec (CommRingCat.of A) ⟶ ModularCurve.TwoChartModel A (↥K) j),
      (∀ a : A, ψ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) a) = a) ∧
      ψ (ModularCurve.TwoChart.jInvChartInf A (↥K) j) = 0 ∧
      (∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
        algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0) ∧
      ε = Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιInf A (↥K) j ∧
      ε ≫ ModularCurve.TwoChart.modelTo A (↥K) j = 𝟙 _ ∧
      (∀ y : ↥(Spec (CommRingCat.of A)), ε.base y ∉ Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringHom_section_comp_iotaInf_modelTo_of_coe_eq_coeffEmb_jq.solution
