import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_subring_etaleCoordinate_residueChar_iff_charts_of_smooth_of_isDiscreteValuationRing
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def
attribute [-simp] AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen
attribute [-simp] ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing open AlgebraicCurve hiding isCurveOver_of_transcendental

theorem AlgebraicCurve.TwoChartIntegralModel.exists_subring_etaleCoordinate_residueChar_iff_charts_of_smooth_of_isDiscreteValuationRing
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    [IsAlgClosed (ResidueField A)]
    {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    {F : Type} [Field F] [Algebra L F] [Algebra A F] [IsScalarTower A L F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental L j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set F)) F)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel A F j))
    (hx : (TwoChartIntegralModel.toBase A F j).base x = closedPoint A)
    (hxc : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A F j), x ⤳ y → y = x)
    (hxs : ∃ U : (AlgebraicCurve.TwoChartIntegralModel A F j).Opens,
      x ∈ U ∧ Smooth (U.ι ≫ TwoChartIntegralModel.toBase A F j)) :
    ∃ (S : Subring F) (φ : Polynomial A →+* ↥S) (χ : ↥S →+* ResidueField A),

      (∀ f : F, f ∈ S ↔
        ((∀ y : ↥(TwoChartIntegralModel.XFin A F j), (TwoChartIntegralModel.ιFin A F j).base y = x →
            ∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
         (∀ y : ↥(TwoChartIntegralModel.XInf A F j), (TwoChartIntegralModel.ιInf A F j).base y = x →
            ∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)))) ∧

      (∀ f : ↥S, χ f = 0 ↔
        ((∀ y : ↥(TwoChartIntegralModel.XFin A F j), (TwoChartIntegralModel.ιFin A F j).base y = x →
            ∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ (f : F) * (h : F) = (g : F)) ∧
         (∀ y : ↥(TwoChartIntegralModel.XInf A F j), (TwoChartIntegralModel.ιInf A F j).base y = x →
            ∃ g h : ↥(TwoChartIntegralModel.chartAlgInf A F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ (f : F) * (h : F) = (g : F)))) ∧

      (∀ a : A, algebraMap A F a ∈ S) ∧
      (∀ a : A, ((φ (Polynomial.C a) : ↥S) : F) = algebraMap A F a) ∧
      (∀ a : A, χ (φ (Polynomial.C a)) = IsLocalRing.residue A a) ∧
      χ (φ Polynomial.X) = 0 ∧

      (∃ _ : IsLocalRing ↥S,
        RingHom.ker χ = IsLocalRing.maximalIdeal ↥S ∧
        IsLocalRing.maximalIdeal ↥S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X}) ∧
      Function.Surjective χ ∧

      φ.FormallySmooth ∧ φ.FormallyUnramified ∧ φ.EssFiniteType ∧
      φ Polynomial.X ∉ Ideal.span {φ (Polynomial.C ϖ)} ∧

      (∀ f : F, ∃ g h : ↥S, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧

      IsNoetherianRing ↥S ∧
      (∃ _ : IsDomain (↥S ⧸ Ideal.span {φ (Polynomial.C ϖ)}),
        IsDiscreteValuationRing (↥S ⧸ Ideal.span {φ (Polynomial.C ϖ)})) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_subring_etaleCoordinate_residueChar_iff_charts_of_smooth_of_isDiscreteValuationRing.solution
