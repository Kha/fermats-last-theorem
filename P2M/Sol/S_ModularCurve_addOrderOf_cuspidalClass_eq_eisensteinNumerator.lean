import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_isPrincipal_eisensteinNumerator_smul_cuspidalDivisor
import Theorems.Thm_ModularCurve_exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor
import P2M.Sol.S_AlgebraicCurve_Pic0_mk_eq_zero_iff
import P2M.Sol.S_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal
import P2M.Sol.S_AlgebraicCurve_Pic0_zsmul_mk
import P2M.Util
namespace P2MW.S_ModularCurve_addOrderOf_cuspidalClass_eq_eisensteinNumerator
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

set_option autoImplicit false

noncomputable section

namespace CuspOrder

open ModularCurve AlgebraicCurve

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

theorem eisensteinNumerator_pos : 0 < eisensteinNumerator ℓ := by
  have h := sharpIndex_mul_eisensteinNumerator ℓ
  have h1 : 1 ≤ ℓ - 1 := by have := hℓ.out.two_le; omega
  rcases Nat.eq_zero_or_pos (eisensteinNumerator ℓ) with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0

theorem addOrderOf_cuspidalClass_eq_eisensteinNumerator (_hW : SharpUnitInvariant ℓ)
    (hWnec : SharpUnitNecessary ℓ) : addOrderOf (cuspidalClass ℓ) = eisensteinNumerator ℓ := by
  have hC1 := isPrincipal_eisensteinNumerator_smul_cuspidalDivisor ℓ

  have h1 : addOrderOf (cuspidalClass ℓ) ∣ eisensteinNumerator ℓ := by
    rw [cuspidalClass_def]
    refine Pic0.addOrderOf_mk_dvd_of_isPrincipal _ _ ?_
    rw [coe_cuspidalDivisor₀, ← natCast_zsmul]
    exact hC1

  set d := addOrderOf (cuspidalClass ℓ) with hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at h1
    exact (eisensteinNumerator_pos ℓ).ne' h1
  have hdc : (d : ℤ) • cuspidalClass ℓ = 0 := by
    rw [natCast_zsmul]; exact addOrderOf_nsmul_eq_zero (cuspidalClass ℓ)
  have hP : Divisor.IsPrincipal ((d : ℤ) • cuspidalDivisor ℓ) := by
    have h := hdc
    rw [cuspidalClass_def, Pic0.zsmul_mk, Pic0.mk_eq_zero_iff] at h
    simpa using h
  obtain ⟨H, hcont, hpow, hinv⟩ := exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor ℓ d hdpos hP
  have h2 : eisensteinNumerator ℓ ∣ d := hWnec d H hdpos hcont hpow hinv
  exact Nat.dvd_antisymm h1 h2

end CuspOrder

end

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hW : ModularCurve.SharpUnitInvariant ℓ) (hWnec : ModularCurve.SharpUnitNecessary ℓ) : addOrderOf (ModularCurve.cuspidalClass ℓ) = ModularCurve.eisensteinNumerator ℓ := by
  exact CuspOrder.addOrderOf_cuspidalClass_eq_eisensteinNumerator ℓ hW hWnec
