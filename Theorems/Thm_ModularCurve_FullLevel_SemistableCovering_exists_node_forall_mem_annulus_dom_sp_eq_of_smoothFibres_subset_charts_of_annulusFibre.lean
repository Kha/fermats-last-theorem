import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CategoryTheory AlgebraicGeometry

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : (A : Set (AlgebraicClosure ℚ)) ≠ Set.univ)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (𝒞 : SemistableCovering q M' A W)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : ↥(fieldBar q M') ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ)) =
      SemistableModel.baseToFunctionField toBase a)

    (pt sp : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → X)
    (hpt : ∀ P, SemistableModel.localRing X φ (pt P) = P.toValuationSubring.toSubring ∧ (toBase.base (pt P)).asIdeal = ⊥)
    (hsp : ∀ P, pt P ⤳ sp P ∧ sp P ≠ pt P ∧ toBase.base (sp P) = closedPoint ↥A ∧ (∀ y : X, sp P ⤳ y → y = sp P) ∧
      (∀ y : X, pt P ⤳ y → y = pt P ∨ y = sp P) ∧
      ∀ f : ↥(fieldBar q M'), f ∈ SemistableModel.localRing X φ (sp P) →
        f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ (sp P), f * g = 1))

    (gen : CuspidalType.ProjLine q ⊕ ↥W → X)
    (hgenI : ∀ ℓ, SemistableModel.localRing X φ (gen (Sum.inl ℓ)) = (𝒞.CIg ℓ).integers.toSubring)
    (hgenS : ∀ s, SemistableModel.localRing X φ (gen (Sum.inr s)) = (𝒞.CSS s).integers.toSubring)
    (hgen_sp : ∀ i, toBase.base (gen i) = closedPoint ↥A)
    (hgen : ∀ x : X, toBase.base x = closedPoint ↥A → ((∃ i, x = gen i) ↔ ∃ y : X, x ⤳ y ∧ y ≠ x))

    (hnode : ∀ x : X, toBase.base x = closedPoint ↥A → (∀ y : X, x ⤳ y → y = x) → x ∉ toBase.smoothLocus →
      ∃ i j, i ≠ j ∧ gen i ⤳ x ∧ gen j ⤳ x ∧ (∀ k, gen k ⤳ x → k = i ∨ k = j) ∧
      ∃ (t₁ t₂ u u' : ↥(fieldBar q M')) (μ : ↥A), μ ∈ maximalIdeal ↥A ∧ (μ : AlgebraicClosure ℚ) ≠ 0 ∧
        t₁ ∈ SemistableModel.localRing X φ x ∧ t₂ ∈ SemistableModel.localRing X φ x ∧
        u ∈ SemistableModel.localRing X φ x ∧ u' ∈ SemistableModel.localRing X φ x ∧ u * u' = 1 ∧
        (¬ ∃ g ∈ SemistableModel.localRing X φ x, t₁ * g = 1) ∧ (¬ ∃ g ∈ SemistableModel.localRing X φ x, t₂ * g = 1) ∧
        t₁ * t₂ = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (μ : AlgebraicClosure ℚ) * u ∧

        (∃ g ∈ SemistableModel.localRing X φ (gen i), t₁ * g = 1) ∧ (∃ g ∈ SemistableModel.localRing X φ (gen j), t₂ * g = 1))

    (hAnSp : ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ∃ x : X,
      x ∉ toBase.smoothLocus ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      gen (Sum.inl ℓ) ⤳ x ∧ gen (Sum.inr s) ⤳ x ∧ ∀ P, P ∈ (𝒞.An ℓ s).dom → sp P = x) :
    ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ∃ x : X,
      x ∉ toBase.smoothLocus ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      (∀ P, P ∈ (𝒞.An ℓ s).dom → sp P = x) ∧
      gen (Sum.inl ℓ) ⤳ x ∧ gen (Sum.inr s) ⤳ x ∧
      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (𝒞.CIg ℓ).integers), f ∈ SemistableModel.localRing X φ x →
        (𝒞.CIg ℓ).residue ⟨f, hf⟩ ∈ (𝒞.xs ℓ s).toValuationSubring) ∧
      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (𝒞.CSS s).integers), f ∈ SemistableModel.localRing X φ x →
        (𝒞.CSS s).residue ⟨f, hf⟩ ∈ (𝒞.xt ℓ s).toValuationSubring) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre.solution
