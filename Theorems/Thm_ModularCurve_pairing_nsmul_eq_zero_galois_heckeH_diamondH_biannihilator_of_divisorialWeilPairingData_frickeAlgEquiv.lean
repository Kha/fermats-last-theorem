import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import P2M.Util
import P2M.Sol.S_ModularCurve_pairing_nsmul_eq_zero_galois_heckeH_diamondH_biannihilator_of_divisorialWeilPairingData_frickeAlgEquiv
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC
attribute [-instance] AlgebraicCurve.CellDissection.decEqE ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
attribute [-simp] AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero
attribute [-simp] ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ

set_option autoImplicit false

open ModularCurve open AlgebraicCurve hiding ell

theorem ModularCurve.pairing_nsmul_eq_zero_galois_heckeH_diamondH_biannihilator_of_divisorialWeilPairingData_frickeAlgEquiv
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (n : ℕ) [NeZero n]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H)]
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) n)
    (w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] ModularCurve.xHFunctionFieldBar M H)

    (hw1 : ∀ (ℓ : ℕ) [Fact ℓ.Prime]
        (hα : ModularCurve.HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
        (hβ : ModularCurve.HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
        [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))]
        (hFIβ : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ)
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ)
        (hfinα : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
        (hNα : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ)
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfinα)
        (hFIα : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ)
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
        (hfinβ : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
        (hNβ : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ)
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
        (x : ModularCurve.JH M H),
      ModularCurve.heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (AlgebraicCurve.SemilinearAut.ofAlgAut w • x)
        = AlgebraicCurve.SemilinearAut.ofAlgAut w • ModularCurve.heckePic0HBar hα hβ hFIβ hfinα hNα x)

    (hw2 : ∀ (d : (ZMod M)ˣ) (x : ModularCurve.JH M H),
      ModularCurve.diamondHBar M H d (AlgebraicCurve.SemilinearAut.ofAlgAut w • ModularCurve.diamondHBar M H d x)
        = AlgebraicCurve.SemilinearAut.ofAlgAut w • x)

    (hw4 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ModularCurve.JH M H,
          AlgebraicCurve.SemilinearAut.ofAlgAut w • (σ • x)
            = σ • ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (AlgebraicCurve.SemilinearAut.ofAlgAut w • x))

    (B : ModularCurve.JH M H → ModularCurve.JH M H → AlgebraicClosure ℚ)
    (hB : ∀ (x y : ModularCurve.JH M H) (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0),
      B x y = e.pair ⟨x, AlgebraicCurve.Pic0.mem_torsion.mpr hx⟩
        (AlgebraicCurve.SemilinearAut.ofAlgAut w • ⟨y, AlgebraicCurve.Pic0.mem_torsion.mpr hy⟩)) :
    (∀ x y : JH M H, n • x = 0 → n • y = 0 → B x y ^ n = 1) ∧
    (∀ x x' y : JH M H, n • x = 0 → n • x' = 0 → n • y = 0 → B (x + x') y = B x y * B x' y) ∧
    (∀ x y y' : JH M H, n • x = 0 → n • y = 0 → n • y' = 0 → B x (y + y') = B x y * B x y') ∧
    (∀ x : JH M H, n • x = 0 → (∀ y : JH M H, n • y = 0 → B x y = 1) → x = 0) ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x y : JH M H, n • x = 0 → n • y = 0 →
          B (diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • x)) (σ • y) = σ (B x y)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (x y : JH M H), n • x = 0 → n • y = 0 →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        B (heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x) y =
          B x (heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ y)) ∧
    (∀ (d : (ZMod M)ˣ) (x y : JH M H), n • x = 0 → n • y = 0 →
        B (diamondHBar M H d x) y = B x (diamondHBar M H d y)) ∧

    (∀ y : JH M H, n • y = 0 → (∀ x : JH M H, n • x = 0 → B x y = 1) → y = 0) ∧

    (∀ A : AddSubgroup (JH M H), (∀ a ∈ A, n • a = 0) →
      ∀ x : JH M H, n • x = 0 →
        (∀ y : JH M H, n • y = 0 → (∀ a ∈ A, B a y = 1) → B x y = 1) → x ∈ A) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pairing_nsmul_eq_zero_galois_heckeH_diamondH_biannihilator_of_divisorialWeilPairingData_frickeAlgEquiv.solution
