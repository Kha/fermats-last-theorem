import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) {T R : Type} [CommRing T] [CommRing R] [IsNoetherianRing T] [IsLocalRing R]
    (φ : T →+* R) (hφ : Function.Injective φ)
    (ET : FakeEllipticCurve Λ N T) (E : FakeEllipticCurve Λ N R) (g : E.A ⟶ ET.A)
    (hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom φ)))
    (hlaw : (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
          (E.L.mul t' P Q).1 ≫ g =
            (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
              ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1))
    (hact : ∀ x : ↥Λ, E.act x ≫ g = g ≫ ET.act x) :
    ∃ (T₁ : Type) (_ : CommRing T₁) (_ : IsLocalRing T₁) (_ : IsNoetherianRing T₁) (ψ : T →+* T₁) (φ₁ : T₁ →+* R),
      φ₁.comp ψ = φ ∧ Function.Injective φ₁ ∧ IsLocalHom φ₁ ∧
      ∃ (E₁ : FakeEllipticCurve Λ N T₁) (g₁ : E.A ⟶ E₁.A)
        (hg₁ : CategoryTheory.IsPullback g₁ E.f E₁.f (Spec.map (CommRingCat.ofHom φ₁)))
        (h : E₁.A ⟶ ET.A) (hh : CategoryTheory.IsPullback h E₁.f ET.f (Spec.map (CommRingCat.ofHom ψ))),
        g₁ ≫ h = g ∧
        (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
          (E.L.mul t' P Q).1 ≫ g₁ =
            (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ₁))
              ⟨P.1 ≫ g₁, by rw [Category.assoc, hg₁.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ g₁, by rw [Category.assoc, hg₁.w, ← Category.assoc, Q.2]⟩).1) ∧
        (∀ x : ↥Λ, E.act x ≫ g₁ = g₁ ≫ E₁.act x) ∧
        (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of T₁)) (P Q : SchemeHomOver t' E₁.f),
          (E₁.L.mul t' P Q).1 ≫ h =
            (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ψ))
              ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective.solution
