import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j' : ↥K) (hj' : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) [Fact (j' ≠ 0)] :
    j' ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ∧
    j ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j' ∧
    (∀ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j', ∃ s ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j,
      (∃ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j, s = 1 + j⁻¹ * a) ∧ s * y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ∧
    (∀ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j, ∃ s ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j',
      (∃ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand.solution
