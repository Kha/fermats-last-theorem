import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_inv_mul_thetaL_mul_level_eq_of_heckePic0Fibre_self_eq_of_smul_eq_neg
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qExpandAlgHomC_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar
attribute [-simp] ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ

open ModularCurve AlgebraicCurve

theorem ModularCurve.coeff_inv_mul_thetaL_mul_level_eq_of_heckePic0Fibre_self_eq_of_smul_eq_neg
    (k : Type*) [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    (τ : modularFunctionFieldC k p ≃ₐ[k] modularFunctionFieldC k p)
    (hτ₁ : τ ⟨jqModC k, jqModC_mem k p⟩ = ⟨jqNModC k p, jqNModC_mem k p⟩)
    (hτ₂ : τ ⟨jqNModC k p, jqNModC_mem k p⟩ = ⟨jqModC k, jqModC_mem k p⟩)
    (D : Divisor k (modularFunctionFieldC k p))
    (hD0 : D ∈ Divisor.degZero (K := k) (F := modularFunctionFieldC k p))
    (f : modularFunctionFieldC k p) (hf : f ≠ 0)
    (hD : ∀ v : Place k (modularFunctionFieldC k p), (q : ℤ) * D v = v.ord f)
    (hU : heckePic0Fibre k p p (Pic0.mk ⟨D, hD0⟩) = Pic0.mk ⟨D, hD0⟩)
    (hw : τ • Pic0.mk ⟨D, hD0⟩ = -Pic0.mk ⟨D, hD0⟩) (n : ℤ) :
    ((f : LaurentSeries k)⁻¹ * thetaL k (f : LaurentSeries k)).coeff (n * p) =
      ((f : LaurentSeries k)⁻¹ * thetaL k (f : LaurentSeries k)).coeff n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_inv_mul_thetaL_mul_level_eq_of_heckePic0Fibre_self_eq_of_smul_eq_neg.solution
