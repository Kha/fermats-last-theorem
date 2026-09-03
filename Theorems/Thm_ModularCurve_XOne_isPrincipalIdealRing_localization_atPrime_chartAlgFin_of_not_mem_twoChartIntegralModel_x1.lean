import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_XOne_isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1
attribute [-simp] ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel~isRegularLocalRing_localization_fractionRing_tensor_chartAlgFin"
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XOne.isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (ϖ : A) (hϖ : Irreducible ϖ)
    (K_M : IntermediateField L (LaurentSeries L))
    (hK_M : K_M = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥K_M] [IsScalarTower A L ↥K_M]
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)]
    (𝔪 : Ideal ↥(chartAlgFin A (↥K_M) j_M)) [𝔪.IsMaximal] (hϖ𝔪 : algebraMap A _ ϖ ∉ 𝔪) :
    IsPrincipalIdealRing (Localization.AtPrime 𝔪) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOne_isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1.solution
