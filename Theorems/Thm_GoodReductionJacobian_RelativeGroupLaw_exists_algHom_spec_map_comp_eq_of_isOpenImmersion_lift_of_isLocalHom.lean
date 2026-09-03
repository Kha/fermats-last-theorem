import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_algHom_spec_map_comp_eq_of_isOpenImmersion_lift_of_isLocalHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_algHom_spec_map_comp_eq_of_isOpenImmersion_lift_of_isLocalHom
    {R₀ : Type} [CommRing R₀]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (n : ℕ)
    (Rh : Type) [CommRing Rh] [IsLocalRing Rh] (ρh : R₀ →+* Rh)
    (B : Type) [CommRing B] [Algebra Rh B]
    (ι : Spec (CommRingCat.of B) ⟶ X)
    (h1 : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))
    (h3 : ι ≫ L.schemeNsmul n = (ι ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R₀)))).1)
    (h4 : pullback.lift (f := L.schemeNsmul n) (g := (L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) ι (ι ≫ f) h3 ≫
        (pullback.fst (L.schemeNsmul n) ((L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) ≫ f) =
      Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hopen : IsOpenImmersion (pullback.lift
        (f := pullback.fst (L.schemeNsmul n) ((L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) ≫ f)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := L.schemeNsmul n) (g := (L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) ι (ι ≫ f) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh B))) h4))
    (hcov : ∀ x : ↥(Limits.pullback (pullback.fst (L.schemeNsmul n) ((L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) ≫ f)
                  (Spec.map (CommRingCat.ofHom ρh))),
      (pullback.snd (pullback.fst (L.schemeNsmul n) ((L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) ≫ f)
          (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
        x ∈ Set.range (pullback.lift
          (f := pullback.fst (L.schemeNsmul n) ((L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) ≫ f)
          (g := Spec.map (CommRingCat.ofHom ρh))
          (pullback.lift (f := L.schemeNsmul n) (g := (L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) ι (ι ≫ f) h3)
          (Spec.map (CommRingCat.ofHom (algebraMap Rh B))) h4).base)
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra Rh T] [IsLocalHom (algebraMap Rh T)]
    (s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Rh T)) ≫ Spec.map (CommRingCat.ofHom ρh)) f)
    (hs : s.1 ≫ L.schemeNsmul n =
      (Spec.map (CommRingCat.ofHom (algebraMap Rh T)) ≫ Spec.map (CommRingCat.ofHom ρh)) ≫ (L.one (𝟙 (Spec (CommRingCat.of R₀)))).1) :
    ∃ φ : B →ₐ[Rh] T, Spec.map (CommRingCat.ofHom (φ : B →+* T)) ≫ ι = s.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_algHom_spec_map_comp_eq_of_isOpenImmersion_lift_of_isLocalHom.solution
