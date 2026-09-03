import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_isUnit_isPullback_section_of_isPullback
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_isUnit_isPullback_section_of_isPullback
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (PP : E.FullLevel m)
    (R : Subalgebra ℤ L) (hR : R.FG) (ER : FakeEllipticCurve Λ N ↥R)
    (g : E.A ⟶ ER.A) (hg : CategoryTheory.IsPullback g E.f ER.f (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hER :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (ER.L.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ ER.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' E.f),
        FactorsThrough E.lev P → ∃ P₀ : T ⟶ ER.C, P₀ ≫ ER.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' E.f),
        (∃ P₀ : T ⟶ ER.C, P₀ ≫ ER.lev = P.1 ≫ g) → FactorsThrough E.lev P))
    (PR : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R))) ER.f)
    (hPR : PP.P.1 ≫ g = Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ PR.1)
    (hPRtor : nsmulPt ER.L (𝟙 (Spec (CommRingCat.of ↥R))) m PR = ER.L.one (𝟙 (Spec (CommRingCat.of ↥R))))
    (hm : IsUnit ((m : ℕ) : L)) (s : Finset L) :
    ∃ (R' : Subalgebra ℤ L) (_ : R'.FG) (hRR' : R ≤ R') (_ : (↑s : Set L) ⊆ R') (_ : IsUnit ((m : ℕ) : ↥R'))
      (E' : FakeEllipticCurve Λ N ↥R') (g' : E'.A ⟶ ER.A)
      (hg' : CategoryTheory.IsPullback g' E'.f ER.f (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom)))
      (P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R'))) E'.f)
      (gL : E.A ⟶ E'.A) (hgL : CategoryTheory.IsPullback gL E.f E'.f (Spec.map (CommRingCat.ofHom R'.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥R')) (P Q : SchemeHomOver t' E'.f),
        (E'.L.mul t' P Q).1 ≫ g' =
          (ER.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom))
            ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E'.act x ≫ g' = g' ≫ ER.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥R')) (P : SchemeHomOver t' E'.f),
        FactorsThrough E'.lev P → ∃ P₀ : T ⟶ ER.C, P₀ ≫ ER.lev = P.1 ≫ g') ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥R')) (P : SchemeHomOver t' E'.f),
        (∃ P₀ : T ⟶ ER.C, P₀ ≫ ER.lev = P.1 ≫ g') → FactorsThrough E'.lev P) ∧
      P'.1 ≫ g' = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom) ≫ PR.1 ∧
      nsmulPt E'.L (𝟙 (Spec (CommRingCat.of ↥R'))) m P' = E'.L.one (𝟙 (Spec (CommRingCat.of ↥R'))) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ gL =
          (E'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom R'.val.toRingHom))
            ⟨P.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ gL = gL ≫ E'.act x) ∧
      PP.P.1 ≫ gL = Spec.map (CommRingCat.ofHom R'.val.toRingHom) ≫ P'.1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_isUnit_isPullback_section_of_isPullback.solution
