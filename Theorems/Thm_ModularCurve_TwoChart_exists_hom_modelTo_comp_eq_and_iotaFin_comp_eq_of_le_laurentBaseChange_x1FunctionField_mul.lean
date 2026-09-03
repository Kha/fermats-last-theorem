import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_TwoChart_exists_hom_modelTo_comp_eq_and_iotaFin_comp_eq_of_le_laurentBaseChange_x1FunctionField_mul
attribute [-instance] AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin
attribute [-simp] AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.TwoChart.exists_hom_modelTo_comp_eq_and_iotaFin_comp_eq_of_le_laurentBaseChange_x1FunctionField_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (KM : IntermediateField L (LaurentSeries L))
    (hKM : KM = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥KM] [IsScalarTower A L ↥KM]
    (jM : ↥KM) (hjM : ((jM : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jM ≠ 0)]
    (hle : KM ≤ K) :
    ∃ (f : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥KM) jM)
      (ιF : ↥(ModularCurve.TwoChart.chartAlgFin A (↥KM) jM) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
      (ιI : ↥(ModularCurve.TwoChart.chartAlgInf A (↥KM) jM) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)),

      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥KM) jM), (((ιF b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) = ((b : ↥KM) : LaurentSeries L)) ∧
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥KM) jM), (((ιI b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : ↥K) : LaurentSeries L) = ((b : ↥KM) : LaurentSeries L)) ∧

      f ≫ ModularCurve.TwoChart.modelTo A (↥KM) jM = ModularCurve.TwoChart.modelTo A (↥K) j ∧

      ModularCurve.TwoChart.ιFin A (↥K) j ≫ f = Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥KM) jM ∧
      ModularCurve.TwoChart.ιInf A (↥K) j ≫ f = Spec.map (CommRingCat.ofHom ιI.toRingHom) ≫ ModularCurve.TwoChart.ιInf A (↥KM) jM ∧

      f ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥KM) jM).opensRange = (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange ∧
      f ⁻¹ᵁ (ModularCurve.TwoChart.ιInf A (↥KM) jM).opensRange = (ModularCurve.TwoChart.ιInf A (↥K) j).opensRange ∧

      IsFinite f ∧ Function.Surjective f.base := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TwoChart_exists_hom_modelTo_comp_eq_and_iotaFin_comp_eq_of_le_laurentBaseChange_x1FunctionField_mul.solution
