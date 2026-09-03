import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (gA : A' ⟶ A) (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t'' f'),
      (L'.mul t'' x y).1 ≫ gA =
        (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (𝓛 : A.Modules) (𝓛' : A'.Modules)
    {R R' : Type} [CommRing R] [CommRing R'] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S')) (ψ : R →+* R')
    (hr : Spec.map (CommRingCat.ofHom ψ) ≫ t = t' ≫ Spec.map (CommRingCat.ofHom φ))
    (b : pullback f' t' ⟶ pullback f t) (hb₁ : b ≫ pullback.fst f t = pullback.fst f' t' ≫ gA)
    (hb₂ : b ≫ pullback.snd f t = pullback.snd f' t' ≫ Spec.map (CommRingCat.ofHom ψ))
    (c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.fst f' t')).obj 𝓛') :
    ∃ β : ThetaPt f L 𝓛 t →* ThetaPt f' L' 𝓛' t',
      (∀ θ : ThetaPt f L 𝓛 t, (β θ).pt.1 ≫ gA = Spec.map (CommRingCat.ofHom ψ) ≫ θ.pt.1) ∧
      (∀ (θ : ThetaPt f L 𝓛 t) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        (β θ).act (c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b s :
            Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (θ.act s) :
            Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) ∧
      (∀ u : Rˣ, β (ThetaPt.ofScalar u) = ThetaPt.ofScalar (Units.map (ψ : R →* R') u)) ∧
      (∀ v : Γ(pullback f t, ⊤)ˣ,
        β (ThetaPt.ofUnit v) = ThetaPt.ofUnit (Units.map (b.appTop.hom : Γ(pullback f t, ⊤) →* Γ(pullback f' t', ⊤)) v)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback.solution
