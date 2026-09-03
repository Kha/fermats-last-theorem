import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N r : ℕ)

    (R : Type) [CommRing R] (𝒪₀ : Type) [CommRing 𝒪₀] (K : Type) [CommRing K] (C : Type) [CommRing C]
    (sbar : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (cK : K →+* C) (c₀ : 𝒪₀ →+* C)

    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (ar : 𝒳₀ ⟶ 𝒳₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)

    (u : pullback πX (Spec.map (CommRingCat.ofHom cK) ≫ sbar) ≅ pullback f₀ (Spec.map (CommRingCat.ofHom c₀)))
    (hupt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of C)) (E : FakeEllipticCurve Λ N S),
      pullback.lift (pt S (s ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) E).1 s
          (pt S (s ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) E).2 ≫ u.hom =
        pullback.lift (pt₀ S (s ≫ Spec.map (CommRingCat.ofHom c₀)) E).1 s
          (pt₀ S (s ≫ Spec.map (CommRingCat.ofHom c₀)) E).2)

    (aC : pullback f₀ (Spec.map (CommRingCat.ofHom c₀)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom c₀)))
    (haC₁ : aC ≫ pullback.fst f₀ (Spec.map (CommRingCat.ofHom c₀)) = pullback.fst f₀ (Spec.map (CommRingCat.ofHom c₀)) ≫ ar)
    (haC₂ : aC ≫ pullback.snd f₀ (Spec.map (CommRingCat.ofHom c₀)) = pullback.snd f₀ (Spec.map (CommRingCat.ofHom c₀)))

    (E E' : FakeEllipticCurve Λ N K) (hEE' : FakeEllipticCurve.IsAtkinLehnerQuotient r E E') :
    (pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E).1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E).2, Category.id_comp]) ≫ u.hom) ≫ aC =
      pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E').1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E').2, Category.id_comp]) ≫ u.hom := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient.solution
