import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (h𝒜 : AbelianSchemePropertyBundle R f)
    {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)} (LP : RelativeGroupLaw K fP)
    (g : P ⟶ 𝒜) (hg : CategoryTheory.IsPullback g fP f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fP),
      (LP.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (act : ↥Λ → (P ⟶ P)) (act_over : ∀ x : ↥Λ, act x ≫ fP = fP)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u v : SchemeHomOver t fP),
      pushPt (act x) (act_over x) (LP.mul t u v) =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act x) (act_over x) v))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 P)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u : SchemeHomOver t fP),
      pushPt (act (x + y)) (act_over (x + y)) u =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act y) (act_over y) u)) :
    ∃ (act' : ↥Λ → (𝒜 ⟶ 𝒜)) (act'_over : ∀ x : ↥Λ, act' x ≫ f = f),
      (∀ x : ↥Λ, act x ≫ g = g ≫ act' x) ∧
      (∀ (x : ↥Λ) (ψ : 𝒜 ⟶ 𝒜), ψ ≫ f = f → act x ≫ g = g ≫ ψ → ψ = act' x) ∧
      (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t f),
        pushPt (act' x) (act'_over x) (L.mul t u v) =
          L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' x) (act'_over x) v)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act' ⟨1, h⟩ = 𝟙 𝒜) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act' ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act' y ≫ act' x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver t f),
        pushPt (act' (x + y)) (act'_over (x + y)) u =
          L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' y) (act'_over y) u)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.solution
