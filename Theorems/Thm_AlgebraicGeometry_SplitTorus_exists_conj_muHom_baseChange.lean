import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_exists_conj_muHom_baseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus IsLocalRing

theorem AlgebraicGeometry.SplitTorus.exists_conj_muHom_baseChange
    {R₀ : Type u} [CommRing R₀] {A : Type u} [CommRing A] [IsLocalRing A]
    (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R₀))
    (s : A ≃+* A) (hs : Spec.map (CommRingCat.ofHom s.toRingHom) ≫ σ = σ)

    (sbar : ResidueField A →+* ResidueField A) (hsbar : sbar.comp (residue A) = (residue A).comp s.toRingHom)
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) (L : RelativeGroupLaw R₀ g)
    (t m : ℕ) (ι : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g)) :
    ∃ ι' : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),

      ι'.1 ≫ pullback.fst g σ = muBaseChange s.toRingHom t m ≫ ι.1 ≫ pullback.fst g σ ∧

      ((∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
          NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι =
            (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι)
              (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι)) →
        ∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
          NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι' =
            (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι')
              (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι')) ∧

      (IsClosedImmersion ι.1 → IsClosedImmersion ι'.1) ∧

      muBaseChange (residue A) t m ≫ ι'.1 ≫ pullback.fst g σ =
        muBaseChange sbar t m ≫ muBaseChange (residue A) t m ≫ ι.1 ≫ pullback.fst g σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_exists_conj_muHom_baseChange.solution
