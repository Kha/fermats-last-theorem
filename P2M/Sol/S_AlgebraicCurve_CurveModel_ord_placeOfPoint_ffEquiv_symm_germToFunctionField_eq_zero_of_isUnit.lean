import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Sol.S_AlgebraicCurve_Place_mem_iff_ord_nonneg
import P2M.Util
namespace P2MW.S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
attribute [-simp] AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (Mc : AlgebraicCurve.CurveModel K L)
    (U : Mc.C.Opens) (P : closedPoints Mc.C) (hP : P.1 ∈ U)
    [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(Mc.C, U)) (hs : IsUnit s) :
    (Mc.placeOfPoint P).ord (Mc.ffEquiv.symm (Mc.C.germToFunctionField U s)) = 0 := by

  let φ : Mc.C.presheaf.stalk P.1 →+* L :=
    (Mc.ffEquiv.symm : Mc.C.functionField ≃+* L).toRingHom.comp (algebraMap (Mc.C.presheaf.stalk P.1) Mc.C.functionField)
  have hrange : φ.range = (Mc.placeOfPoint P).toValuationSubring.toSubring := Mc.range_stalk_eq P

  let g : Mc.C.presheaf.stalk P.1 := Mc.C.presheaf.germ U P.1 hP s
  have hg : IsUnit g := hs.map _
  have hgerm : Mc.C.germToFunctionField U s = algebraMap (Mc.C.presheaf.stalk P.1) Mc.C.functionField g := by
    change algebraMap Γ(Mc.C, U) Mc.C.functionField s = _
    exact IsScalarTower.algebraMap_apply Γ(Mc.C, U) (Mc.C.presheaf.stalk ((⟨P.1, hP⟩ : U) : Mc.C)) Mc.C.functionField s
  have hx : Mc.ffEquiv.symm (Mc.C.germToFunctionField U s) = φ g := by
    rw [hgerm]
    rfl
  rw [hx]

  have hmem : ∀ t : Mc.C.presheaf.stalk P.1, φ t ∈ (Mc.placeOfPoint P).toValuationSubring := fun t => by
    have ht : φ t ∈ φ.range := ⟨t, rfl⟩
    rw [hrange] at ht
    exact ht
  have hinv : φ g * φ ((hg.unit⁻¹ : (Mc.C.presheaf.stalk P.1)ˣ) : Mc.C.presheaf.stalk P.1) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have hne : φ g ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have h1 : 0 ≤ (Mc.placeOfPoint P).ord (φ g) :=
    ((Mc.placeOfPoint P).mem_iff_ord_nonneg hne).mp (hmem g)
  have hinv' : (φ g)⁻¹ = φ ((hg.unit⁻¹ : (Mc.C.presheaf.stalk P.1)ˣ) : Mc.C.presheaf.stalk P.1) :=
    (eq_inv_of_mul_eq_one_right hinv).symm ▸ rfl
  have h2 : 0 ≤ (Mc.placeOfPoint P).ord (φ g)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((Mc.placeOfPoint P).mem_iff_ord_nonneg (fun h0 => by
      rw [← inv_eq_of_mul_eq_one_right hinv] at h0
      exact (inv_ne_zero hne) h0)).mp (hmem _)
  rw [AlgebraicCurve.Place.ord_inv] at h2
  omega
