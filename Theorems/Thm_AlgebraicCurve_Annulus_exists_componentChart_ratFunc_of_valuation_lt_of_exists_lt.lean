import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
attribute [-instance] AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
attribute [-simp] AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open Classical in

theorem AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type*) [Field F] [Algebra L F] [IsCurveOver L F]
    (An : Annulus A F)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (Qinf : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
    (hQinf : (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∉ Qinf.toValuationSubring) :
    ∃ Cc : ComponentChart A F (RatFunc (IsLocalRing.ResidueField A)),

      Cc.dom = {P | P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c} ∧
      Cc.nodes = {placeOfPoint (IsLocalRing.ResidueField A) 0, Qinf} ∧
      (∃ h : (algebraMap L F c)⁻¹ * An.param ∈ Cc.integers,
          Cc.residue ⟨_, h⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))) ∧
      (∀ P ∈ Cc.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
          Cc.placeMap P = placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨_, h⟩)) ∧

      (∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q ∉ Cc.nodes →
        ∃ (T : F) (hT : T ∈ Cc.integers), Cc.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (Cc.residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ Cc.dom, Cc.placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c' : A, c' ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place L F, P ∈ Cc.dom ∧ Cc.placeMap P = Q ∧ P.evalAt T = c') ∧

      (∀ P ∈ Cc.dom, P.IsRational) ∧

      (∀ b : L, A.valuation ((An.modulus : A) : L) ≤ A.valuation b → A.valuation b < A.valuation c →
        ∀ (f : F) (hf : f ∈ Cc.integers), Cc.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation c → P.ord f = 0) →
          ∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation c →
            ∃ h : P.evalAt f * (c⁻¹ * P.evalAt An.param) ^
                (-((placeOfPoint (IsLocalRing.ResidueField A) 0).ord (Cc.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) ∧

      (∀ a : L, A.valuation c < A.valuation a → A.valuation a ≤ 1 →
        ∀ (f : F) (hf : f ∈ Cc.integers), Cc.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation a → P.ord f = 0) →
          ∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation a →
            ∃ h : P.evalAt f * (c * (P.evalAt An.param)⁻¹) ^
                (-(Qinf.ord (Cc.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt.solution
