import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (hΓ : ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
    (r : S) (B : Type u) [CommRing B] [Algebra S B] [IsLocalization.Away r B]
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of B)) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) :
    Function.Surjective (f'.appTop).hom ∧
      ∀ r' : B, Function.Surjective
        ((pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r'))))).appTop).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away.solution
