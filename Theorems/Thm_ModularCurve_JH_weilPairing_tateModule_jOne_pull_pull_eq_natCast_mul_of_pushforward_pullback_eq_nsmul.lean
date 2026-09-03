import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_ModularCurve_JH_weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X
attribute [-simp] ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none RatFunc.denom_X_pow RatFunc.powerBasisAdjoinXPow_dim RatFunc.powerBasisAdjoinXPow_gen RatFunc.intDegree_X_pow RatFunc.num_X_pow

set_option autoImplicit false

open AlgebraicCurve open ModularCurve hiding finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar

theorem ModularCurve.JH.weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]

    (ζ : ℕ → AlgebraicClosure ℚ) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (p ^ n))

    (eH : TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] ℤ_[p])
    (heH : ∀ (n : ℕ)
        (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (p ^ n))
        (a b : TateModule p (ModularCurve.JH M H))
        (a' b' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (p ^ n)),
        (a' : ModularCurve.JH M H) = (a : ℕ → ModularCurve.JH M H) n →
        (b' : ModularCurve.JH M H) = (b : ℕ → ModularCurve.JH M H) n →
        W.pair a' b' = ζ n ^ ((eH a b).appr n))

    (e₁ : TateModule p (ModularCurve.JOne M) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne M) →ₗ[ℤ_[p]] ℤ_[p])
    (he₁ : ∀ (n : ℕ)
        (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) (p ^ n))
        (a b : TateModule p (ModularCurve.JOne M))
        (a' b' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) (p ^ n)),
        (a' : ModularCurve.JOne M) = (a : ℕ → ModularCurve.JOne M) n →
        (b' : ModularCurve.JOne M) = (b : ℕ → ModularCurve.JOne M) n →
        W.pair a' b' = ζ n ^ ((e₁ a b).appr n))

    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))

    (pull : ModularCurve.JH M H →+ ModularCurve.JOne M) (push : ModularCurve.JOne M →+ ModularCurve.JH M H) (c : ℕ)
    (hpinPull : ∀ (hint : ι.toRingHom.IsIntegral)
        (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
        (x : ModularCurve.JH M H),
      pull x = AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x)
    (hpinPush : ∀ (hint : ι.toRingHom.IsIntegral)
        (hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι)
        (hN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) ι hfin)
        (y : ModularCurve.JOne M),
      push y = AlgebraicCurve.Pic0.pushforwardAlongHom ι hint hfin hN y)
    (hdeg : ∀ x : ModularCurve.JH M H, push (pull x) = c • x)

    (tpull : TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne M))
    (htpull : ∀ (a : TateModule p (ModularCurve.JH M H)) (n : ℕ),
      ((tpull a : TateModule p (ModularCurve.JOne M)) : ℕ → ModularCurve.JOne M) n =
        pull ((a : ℕ → ModularCurve.JH M H) n))
    (a b : TateModule p (ModularCurve.JH M H)) :
    e₁ (tpull a) (tpull b) = (c : ℤ_[p]) * eH a b := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JH_weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul.solution
