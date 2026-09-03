import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_genericFibre_squares_of_isPullback_inf
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_genericFibre_squares_of_isPullback_inf
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ι₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥O)
    (hι₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (j₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥K')
    (hj₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), ((j₀ x : ↥K') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (𝒜₀ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K'.toSubring)) (𝒜 : FakeEllipticCurve Λ N ↥O)
    (h𝒜₀ : FakeEllipticCurve.IsPullback ι₀ 𝒜₀ 𝒜)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x) :
    ∃ (E₀ : FakeEllipticCurve Λ N ↥K')
      (p : 𝒜.A ⟶ 𝒜₀.A) (hp : CategoryTheory.IsPullback p 𝒜.f 𝒜₀.f (Spec.map (CommRingCat.ofHom ι₀)))
      (g₀ : E₀.A ⟶ 𝒜₀.A) (hg₀ : CategoryTheory.IsPullback g₀ E₀.f 𝒜₀.f (Spec.map (CommRingCat.ofHom j₀)))
      (gE' : E.A ⟶ E₀.A)
      (hgE' : CategoryTheory.IsPullback gE' E.f E₀.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t' 𝒜.f),
        (𝒜.L.mul t' P Q).1 ≫ p =
          (𝒜₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ι₀))
            ⟨P.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ p = p ≫ 𝒜₀.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K')) (P Q : SchemeHomOver t' E₀.f),
        (E₀.L.mul t' P Q).1 ≫ g₀ =
          (𝒜₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j₀))
            ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₀.act x ≫ g₀ = g₀ ≫ 𝒜₀.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ gE' =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
            ⟨P.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ gE' = gE' ≫ E₀.act x) ∧
      gE ≫ p = gE' ≫ g₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_genericFibre_squares_of_isPullback_inf.solution
