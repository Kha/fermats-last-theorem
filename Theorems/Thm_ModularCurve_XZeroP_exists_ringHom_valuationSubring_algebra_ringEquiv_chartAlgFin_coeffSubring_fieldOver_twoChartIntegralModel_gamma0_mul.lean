import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ

set_option autoImplicit false

open AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XZeroP.exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (e : L →+* AlgebraicClosure ℚ)
      (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K)
      (_ : ∀ x : AlgebraicClosure ℚ, x ∈ K ↔ x ∈ Set.range e)
      (Ab : ValuationSubring (AlgebraicClosure ℚ)) (_ : Ab.LiesOverPrime p)
      (hA : ∀ a : A, e (algebraMap A L a) ∈ Ab)

      (_ : ∀ a : A, (⟨e (algebraMap A L a), hA a⟩ : ↥Ab) ∈ IsLocalRing.maximalIdeal ↥Ab ↔ a ∈ IsLocalRing.maximalIdeal A)
      (_ : ∀ x : AlgebraicClosure ℚ, x ∈ ModularCurve.NodeLocalized.coeffSubring Ab K ↔ ∃ a : A, x = e (algebraMap A L a))
      (ϖb : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K))
      (_ : (ϖb : AlgebraicClosure ℚ) = e (algebraMap A L ϖ))
      (_ : ∀ d : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K),
        ModularCurve.NodeLocalized.redRestrict (IsLocalRing.residue ↥Ab) K d = 0 ↔ ∃ d', d = ϖb * d')
      (ε : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) (_ : IsUnit ε)
      (_ : ((p : ℕ) : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) = ϖb ^ (p - 1) * ε)

      (_ : ∀ y : LaurentSeries (AlgebraicClosure ℚ),
        y ∈ ModularCurve.NodeLocalized.fieldOver (M * p) K ↔
          ∃ x : ↥K₂, ModularCurve.coeffMap e ((x : ↥K₂) : LaurentSeries L) = y)

      (inst : Algebra ↥(ModularCurve.NodeLocalized.coeffSubring Ab K) ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K))
      (_ : ∀ c : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K),
        ((algebraMap ↥(ModularCurve.NodeLocalized.coeffSubring Ab K) ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K) c :
            ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.CharPReduction.constSeries (ModularCurve.NodeLocalized.coeffSubring Ab K) c)
      (jK : ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K))
      (_ : ((jK : ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.jqModC (AlgebraicClosure ℚ))
      (_ : Fact (jK ≠ 0))
      (Φ : ↥(chartAlgFin A (↥K₂) j₂) ≃+*
        ↥(chartAlgFin ↥(ModularCurve.NodeLocalized.coeffSubring Ab K) ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K) jK)),
      (∀ b : ↥(chartAlgFin A (↥K₂) j₂),
        (((Φ b : ↥(chartAlgFin ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)
            ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K) jK)) :
            ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.coeffMap e ((b : ↥K₂) : LaurentSeries L)) ∧

      ∃ Ψ : ↥(chartAlgFin A (↥K₂) j₂) ≃+* ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K),
        ∀ b : ↥(chartAlgFin A (↥K₂) j₂),
          ((Ψ b : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) =
            ModularCurve.coeffMap e ((b : ↥K₂) : LaurentSeries L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul.solution
