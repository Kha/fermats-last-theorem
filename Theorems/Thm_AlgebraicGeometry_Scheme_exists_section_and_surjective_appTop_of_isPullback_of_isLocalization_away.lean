import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away
    {B C : Type u} [CommRing B] [CommRing C] [Algebra B C] (t₀ : B) [IsLocalization.Away t₀ C]
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of B)) (e : Spec (CommRingCat.of B) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ : Function.Surjective (f.appTop).hom ∧
      ∀ t : B, Function.Surjective
        ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))))).appTop).hom)
    (f' : A' ⟶ Spec (CommRingCat.of C)) (g : A' ⟶ A)
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap B C)))) :
    ∃ e' : Spec (CommRingCat.of C) ⟶ A',
      e' ≫ f' = 𝟙 _ ∧ e' ≫ g = Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ e ∧
      Function.Surjective (f'.appTop).hom ∧
      ∀ r' : C, Function.Surjective
        ((pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r'))))).appTop).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away.solution
