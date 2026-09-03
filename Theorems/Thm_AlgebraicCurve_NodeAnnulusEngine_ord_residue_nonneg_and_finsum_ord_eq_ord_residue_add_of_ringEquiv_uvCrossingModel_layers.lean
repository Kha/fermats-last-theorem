import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
attribute [-instance] AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instTopologicallyFGOfFiniteType
attribute [-simp] AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk
attribute [-simp] ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec
attribute [-simp] ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeAnnulusEngine.ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩 : Subring F)
    (h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring)
    (hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A)

    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)

    (hx₁r : x₁.IsRational) (hx₂r : x₂.IsRational)

    {Λ : Type*}
    (C' : Λ → Subring L) (hC'A : ∀ (l) (c : L), c ∈ C' l → c ∈ A)
    [∀ l, IsDomain ↥(C' l)] [∀ l, IsDiscreteValuationRing ↥(C' l)]
    (ϖ' : ∀ l, ↥(C' l))
    (hϖ' : ∀ (l) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : L), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d')
    (l₀ : Λ) (hl₀ : ∀ l, C' l₀ ≤ C' l) (hϖ0 : ((ϖ' l₀ : ↥(C' l₀)) : L) ≠ 0)
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥(C' l₀) a)

    (x y u : F) (E₀ : ℕ)
    (hxy : x * y = algebraMap L F ((ϖ' l₀ : ↥(C' l₀)) : L) ^ E₀ * u)

    (𝒩₀ : Λ → Subring F) (h𝒩₀ : ∀ l, 𝒩₀ l ≤ 𝒩) [∀ l, IsLocalRing ↥(𝒩₀ l)] [∀ l, IsNoetherianRing ↥(𝒩₀ l)]

    (hS : ∀ (l) (P : Place L F), P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ l → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥(𝒩₀ l), ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (l : Λ) (a b : ↥(𝒩₀ l)), (b : F) ≠ 0 ∧ f * (b : F) = (a : F))

    (hmono : ∀ l, 𝒩₀ l₀ ≤ 𝒩₀ l)
    (hgen₀ : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥(𝒩₀ l₀)) (b : ↥(𝒩₀ l₀)),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥(𝒩₀ l₀)) : F))
    (hCmem : ∀ (l) (c : L), c ∈ C' l → algebraMap L F c ∈ 𝒩₀ l)
    (hres : ∀ (l) (g : ↥(𝒩₀ l)), ∃ o : ↥(C' l), ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem l o o.2⟩))

    (hld : ∀ (l : Λ) (n : ℕ) (c : Fin n → L) (a : Fin n → ↥(𝒩₀ l)), LinearIndependent ↥(C' l) c →
      ∑ i, c i • ((a i : ↥(𝒩₀ l)) : F) = 0 → ∀ i, a i = 0)
    (hxmem : ∀ l, x ∈ 𝒩₀ l) (hymem : ∀ l, y ∈ 𝒩₀ l) (humem : ∀ l, u ∈ 𝒩₀ l)
    (hu : ∀ l, IsUnit (⟨u, humem l⟩ : ↥(𝒩₀ l)))

    (W : Λ → Type*) [∀ l, CommRing (W l)] [∀ l, IsDomain (W l)] [∀ l, IsDiscreteValuationRing (W l)]
    [∀ l, IsAdicComplete (maximalIdeal (W l)) (W l)]
    (π : ∀ l, W l) (hπ : ∀ l, Irreducible (π l))
    (σ : ∀ l, W l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ l)) ↥(𝒩₀ l))
    (hσπ : ∀ l, σ l (π l) = algebraMap ↥(𝒩₀ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ l)) ↥(𝒩₀ l))
      ⟨algebraMap L F ((ϖ' l : ↥(C' l)) : L), hCmem l _ (ϖ' l).2⟩)
    (E : Λ → ℕ) (hE : ∀ l, 1 ≤ E l)
    (ι : ∀ l, AdicCompletion (maximalIdeal ↥(𝒩₀ l)) ↥(𝒩₀ l) ≃+* UVCrossingModel (W l) (π l ^ E l))
    (hconst : ∀ (l) (o : W l), ι l (σ l o) = const (π l ^ E l) o)
    (hCW : ∀ (l) (c : ↥(C' l)), ∃ o : W l,
      σ l o = algebraMap ↥(𝒩₀ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ l)) ↥(𝒩₀ l)) ⟨algebraMap L F (c : L), hCmem l c c.2⟩)
    (hres₁ : ∀ (l) (f : ↥(𝒩₀ l)) (n : ℕ), R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ l f.2)).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ l f.2)).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel (W l) (π l ^ E l), IsUnit γ ∧
          ι l (algebraMap ↥(𝒩₀ l) _ f) - γ * V (π l ^ E l) ^ n ∈ Ideal.span {const (π l ^ E l) (π l), U (π l ^ E l)})
    (hres₂ : ∀ (l) (f : ↥(𝒩₀ l)) (n : ℕ), R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ l f.2)).2.1⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ l f.2)).2.1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel (W l) (π l ^ E l), IsUnit γ ∧
          ι l (algebraMap ↥(𝒩₀ l) _ f) - γ * U (π l ^ E l) ^ n ∈ Ideal.span {const (π l ^ E l) (π l), V (π l ^ E l)})

    (x_fst : ∀ h₁ : x ∈ R₁.integers, R₁.residue ⟨x, h₁⟩ = 0)
    (x_snd : ∀ h₂ : x ∈ R₂.integers, x₂.ord (R₂.residue ⟨x, h₂⟩) = 1)
    (y_snd : ∀ h₂ : y ∈ R₂.integers, R₂.residue ⟨y, h₂⟩ = 0)
    (y_fst : ∀ h₁ : y ∈ R₁.integers, x₁.ord (R₁.residue ⟨y, h₁⟩) = 1) :

    (∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), f ∈ 𝒩 →
      (R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩)) ∧
      (R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩))) ∧

    (∀ (f : F) (e₁ e₂ : L) (h₁ : e₁ • f ∈ R₁.integers) (h₂ : e₂ • f ∈ R₂.integers),
      R₁.residue ⟨e₁ • f, h₁⟩ ≠ 0 → R₂.residue ⟨e₂ • f, h₂⟩ ≠ 0 →
        {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
        ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨e₁ • f, h₁⟩) + x₂.ord (R₂.residue ⟨e₂ • f, h₂⟩)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.solution
