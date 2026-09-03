import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_comparison_monoidHom_of_ringHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.ThetaPt.exists_comparison_monoidHom_of_ringHom
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    {R R' : Type} [CommRing R] [CommRing R'] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (ψ : R →+* R') :
    ∃ (b : pullback f (Spec.map (CommRingCat.ofHom ψ) ≫ t) ⟶ pullback f t)
      (_ : b ≫ pullback.fst f t = pullback.fst f (Spec.map (CommRingCat.ofHom ψ) ≫ t))
      (_ : b ≫ pullback.snd f t = pullback.snd f (Spec.map (CommRingCat.ofHom ψ) ≫ t) ≫ Spec.map (CommRingCat.ofHom ψ))
      (c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
        (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom ψ) ≫ t))).obj 𝓛)
      (β : ThetaPt f L 𝓛 t →* ThetaPt f L 𝓛 (Spec.map (CommRingCat.ofHom ψ) ≫ t)),
      (∀ θ : ThetaPt f L 𝓛 t, (β θ).pt.1 = Spec.map (CommRingCat.ofHom ψ) ≫ θ.pt.1) ∧
      (∀ (θ : ThetaPt f L 𝓛 t) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        (β θ).act (c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b s :
            Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (θ.act s) :
            Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) ∧
      (∀ u : Rˣ, β (ThetaPt.ofScalar u) = ThetaPt.ofScalar (Units.map (ψ : R →* R') u)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_comparison_monoidHom_of_ringHom.solution
