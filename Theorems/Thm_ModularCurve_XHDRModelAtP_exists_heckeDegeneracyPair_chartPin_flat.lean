import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_exists_heckeDegeneracyPair_chartPin_flat
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe
attribute [-simp] ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
  ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup
open scoped MatrixGroups
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_heckeDegeneracyPair_chartPin_flat
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (ℓ : ℕ) [Fact ℓ.Prime] (hβ : haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩; HeckeBetaHDefined M H ℓ) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∃ (πα πβ : SchemeHomOver (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) (toBase p (ΓM M H) hj))
      (_ : IsFinite πα.1) (_ : IsFinite πβ.1) (_ : LocallyOfFinitePresentation πα.1) (_ : LocallyOfFinitePresentation πβ.1)
      (ια ιβ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj))
      (U : (X p (ΓM M H) hj).Opens),

      Function.Surjective πα.1.base ∧ Function.Surjective πβ.1.base ∧

      (∀ b : ↥(chartAlgFin p (ΓM M H) hj),
        (((ια b : ↥(chartAlgFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)))) : LaurentSeries ℚ) =
          ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) ∧
      (∀ b : ↥(chartAlgFin p (ΓM M H) hj),
        (((ιβ b : ↥(chartAlgFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)))) : LaurentSeries ℚ) =
          qExpand ℚ ℓ ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) ∧
      ιFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ιFin p (ΓM M H) hj ∧
      ιFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ιFin p (ΓM M H) hj ∧

      πα.1 ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj).opensRange ∧
      πβ.1 ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj).opensRange ∧

      (∀ x : ↥(X p (ΓM M H) hj), ringKrullDim ((X p (ΓM M H) hj).presheaf.stalk x) ≤ 1 → x ∈ U) ∧
      Flat (πα.1 ∣_ U) ∧ Flat (πβ.1 ∣_ U) ∧
      (∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πα.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) ∧
      (∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_heckeDegeneracyPair_chartPin_flat.solution
