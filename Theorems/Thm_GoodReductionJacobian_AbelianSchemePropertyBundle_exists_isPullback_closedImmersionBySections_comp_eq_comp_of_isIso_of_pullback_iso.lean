import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (L : RelativeGroupLaw R f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (hci : Scheme.Modules.ClosedImmersionBySections M f)
    (σ : SchemeHomOver f f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of R')) (L' : RelativeGroupLaw R' f')
      (_ : AbelianSchemePropertyBundle R' f')
      (M' : A'.Modules) (_ : Scheme.Modules.IsInvertible M') (_ : Scheme.Modules.ClosedImmersionBySections M' f')
      (σ' : SchemeHomOver f' f') (_ : IsIso σ'.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t f'),
        NeronModelInfra.schemeHomOverComp (L'.mul t x y) σ' =
          L'.mul t (NeronModelInfra.schemeHomOverComp x σ') (NeronModelInfra.schemeHomOverComp y σ'))
      (_ : ∀ s : ↥(Spec (CommRingCat.of R')), ∃ U : (Spec (CommRingCat.of R')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ'.1).obj M') ≅
          (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj M'))
      (p : A' ⟶ A) (hp : CategoryTheory.IsPullback p f' f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ p =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback p).obj M ≅ M') ∧
      σ'.1 ≫ p = p ≫ σ.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso.solution
