import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_diamondAutBar_smul_eq_ncard_smul_pullbackAlong_pushforwardAlong
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.ShimuraCoveringData.mk.injEq ModularCurve.ShimuraCoveringData.mk.sizeOf_spec ModularCurve.ShimuraCoveringData.LiftData.mk.sizeOf_spec ModularCurve.ShimuraCoveringData.coe_coverHom ModularCurve.ShimuraCoveringData.LiftData.mk.injEq ModularCurve.coe_inclusionBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero
attribute [-simp] ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one

set_option autoImplicit false

theorem ModularCurve.sum_diamondAutBar_smul_eq_ncard_smul_pullbackAlong_pushforwardAlong
    (M₀ t : ℕ) [NeZero M₀] (hM₀t : Nat.Coprime M₀ t)
    (hdia : ∀ d : ℕ, Nat.Coprime d (M₀ * t) →
      (∃ σ₀ : ModularCurve.x1FunctionField (M₀ * t) ≃ₐ[ℚ] ModularCurve.x1FunctionField (M₀ * t),
          ModularCurve.IsDiamondAut (M₀ * t) d σ₀) ∧
        ∃ σ' : ModularCurve.x1FunctionFieldBar (M₀ * t) ≃ₐ[AlgebraicClosure ℚ]
            ModularCurve.x1FunctionFieldBar (M₀ * t),
          ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ)
            (ModularCurve.diamondAut (M₀ * t) d) σ')
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M₀ * t))]
    (ι : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ t)
      →ₐ[AlgebraicClosure ℚ] ModularCurve.x1FunctionFieldBar (M₀ * t))
    (hι : ∀ x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ t),
      ((ι x : ModularCurve.x1FunctionFieldBar (M₀ * t)) : LaurentSeries (AlgebraicClosure ℚ))
        = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral)
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M₀ * t))) :
    ∑ d ∈ (Finset.range (M₀ * t)).filter (fun d => Nat.Coprime d (M₀ * t) ∧ d ≡ 1 [MOD M₀]),
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M₀ * t) d) • D
      = Set.ncard {d : ℕ | d < M₀ * t ∧ Nat.Coprime d (M₀ * t) ∧ d ≡ 1 [MOD M₀] ∧
            ModularCurve.diamondAutBar (M₀ * t) d = AlgEquiv.refl} •
        AlgebraicCurve.Divisor.pullbackAlong ι hint (AlgebraicCurve.Divisor.pushforwardAlong ι hint D) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_diamondAutBar_smul_eq_ncard_smul_pullbackAlong_pushforwardAlong.solution
