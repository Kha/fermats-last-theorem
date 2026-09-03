import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (S' : Type u) [CommRing S'] [Algebra S S'] {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (T : Type u) [CommRing T] [Algebra S' T] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd f' (Scheme.TwoAffineOpenCover.specMap S' T)) ⊤
    Function.Bijective (algebraMap T Γ(pullback f' (Scheme.TwoAffineOpenCover.specMap S' T), ⊤)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective.solution
