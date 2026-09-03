import Definitions.Def_ModularCurve_QExpansionDiff
import Mathlib.FieldTheory.IntermediateField.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_eq_thetaL_div_of_D_eq_smul
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring

theorem ModularCurve.coe_eq_thetaL_div_of_D_eq_smul (K : Type*) [Field K]
    (F : IntermediateField K (LaurentSeries K)) (f g c₀ : F)
    (h : KaehlerDifferential.D K F f = c₀ • KaehlerDifferential.D K F g)
    (hg : ModularCurve.thetaL K (g : LaurentSeries K) ≠ 0) :
    (c₀ : LaurentSeries K) =
      ModularCurve.thetaL K (f : LaurentSeries K) / ModularCurve.thetaL K (g : LaurentSeries K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_eq_thetaL_div_of_D_eq_smul.solution
