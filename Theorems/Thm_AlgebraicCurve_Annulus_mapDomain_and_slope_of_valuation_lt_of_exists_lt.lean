import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.Annulus.mapDomain_and_slope_of_valuation_lt_of_exists_lt
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A))
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (V : ValuationSubring F)
    (hV : ∀ f : F, f ∈ V ↔ ∃ t : Finset (IsLocalRing.ResidueField A), ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
      A.valuation (P.evalAt An.param) = A.valuation c → IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A)
    (hVA : ∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A)
    (res : ↥V →+* RatFunc (IsLocalRing.ResidueField A))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥V)
    (hconst : ∀ (a : A) (ha : algebraMap L F (a : L) ∈ V),
      res ⟨algebraMap L F (a : L), ha⟩ = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a))
    (hX : ∀ hz : algebraMap L F c⁻¹ * An.param ∈ V, res ⟨algebraMap L F c⁻¹ * An.param, hz⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)))
    (hpt : ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c → P.IsRational →
          ∀ (f : F) (hf : f ∈ V),
            (∀ w ∈ An.dom, ∀ h' : c⁻¹ * w.evalAt An.param ∈ A, A.valuation (w.evalAt An.param) = A.valuation c →
                IsLocalRing.residue A ⟨c⁻¹ * w.evalAt An.param, h'⟩ = IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ → f ∈ w.toValuationSubring) →
            ∃ (hm : (res ⟨f, hf⟩ : RatFunc (IsLocalRing.ResidueField A)) ∈ (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring)
              (hv : P.evalAt f ∈ A),
              algebraMap (IsLocalRing.ResidueField A) (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).ResidueField
                  (IsLocalRing.residue A ⟨P.evalAt f, hv⟩) =
                IsLocalRing.residue (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring ⟨res ⟨f, hf⟩, hm⟩)
    (pm : Place L F → Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
    (hpm : ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
      pm P = placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)) :
    (∀ (f : ↥V), res f ≠ 0 → ∀ D : Divisor L F,
        (∀ P, P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c → D P = P.ord (f : F)) →
        (∀ P, ¬ (P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c) → D P = 0) →
          ∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q ≠ placeOfPoint (IsLocalRing.ResidueField A) 0 →
            (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∈ Q.toValuationSubring →
            Finsupp.mapDomain pm D Q = Q.ord (res f)) ∧
    (∀ (b : L), A.valuation ((An.modulus : A) : L) ≤ A.valuation b → A.valuation b < A.valuation c →
      ∀ (f : F) (hf : f ∈ V), res ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation c → P.ord f = 0) →
        ∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation c →
          ∃ h : P.evalAt f * (c⁻¹ * P.evalAt An.param) ^
              (-((placeOfPoint (IsLocalRing.ResidueField A) 0).ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) ∧
    (∀ (a : L), A.valuation c < A.valuation a → A.valuation a ≤ 1 →
      ∀ (f : F) (hf : f ∈ V), res ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation a → P.ord f = 0) →
        ∀ x : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∉ x.toValuationSubring →
        ∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation a →
          ∃ h : P.evalAt f * (c * (P.evalAt An.param)⁻¹) ^
              (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt.solution
