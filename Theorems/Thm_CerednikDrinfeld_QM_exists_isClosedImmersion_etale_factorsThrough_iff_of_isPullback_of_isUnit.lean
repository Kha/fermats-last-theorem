import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit
attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (h𝒜 : AbelianSchemePropertyBundle R f)
    {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)} (LP : RelativeGroupLaw K fP) (hcP : LP.IsCommutative)
    (hP : AbelianSchemePropertyBundle K fP)
    (g : P ⟶ 𝒜) (hg : CategoryTheory.IsPullback g fP f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fP),
      (LP.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    {ι : Type v} (act : ι → (P ⟶ P)) (act_over : ∀ i : ι, act i ≫ fP = fP)
    (act' : ι → (𝒜 ⟶ 𝒜)) (act'_over : ∀ i : ι, act' i ≫ f = f)
    (hact : ∀ i : ι, act i ≫ g = g ≫ act' i)
    (N : ℕ) (hN : IsUnit ((N : ℕ) : R))
    {C₀ : Scheme.{u}} (lev₀ : C₀ ⟶ P) (lev₀_closed : IsClosedImmersion lev₀)
    (lev₀_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fP),
      FactorsThrough lev₀ x → FactorsThrough lev₀ y →
        FactorsThrough lev₀ (LP.mul t x y) ∧ FactorsThrough lev₀ (LP.inv t x))
    (lev₀_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)), FactorsThrough lev₀ (LP.one t))
    (lev₀_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fP),
      FactorsThrough lev₀ x → nsmulPt LP t N x = LP.one t)
    (lev₀_stable : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fP),
      FactorsThrough lev₀ x → FactorsThrough lev₀ (pushPt (act i) (act_over i) x))
    (lev₀_finite : IsFinite (lev₀ ≫ fP)) (lev₀_flat : Flat (lev₀ ≫ fP))
    (lev₀_rank : ∀ s : ↥(Spec (CommRingCat.of K)), (lev₀ ≫ fP).finrank s = N ^ 2) :
    ∃ (C : Scheme.{u}) (lev : C ⟶ 𝒜), IsClosedImmersion lev ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        FactorsThrough lev x → FactorsThrough lev y →
          FactorsThrough lev (L.mul t x y) ∧ FactorsThrough lev (L.inv t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        FactorsThrough lev x → nsmulPt L t N x = L.one t) ∧
      (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        FactorsThrough lev x → FactorsThrough lev (pushPt (act' i) (act'_over i) x)) ∧
      IsFinite (lev ≫ f) ∧ Flat (lev ≫ f) ∧ LocallyOfFinitePresentation (lev ≫ f) ∧ Etale (lev ≫ f) ∧
      (∀ s : ↥(Spec (CommRingCat.of R)), (lev ≫ f).finrank s = N ^ 2) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t' fP),
        FactorsThrough lev₀ x ↔ ∃ x₀ : T ⟶ C, x₀ ≫ lev = x.1 ≫ g) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.solution
