import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {S S' A₁ X₁ A U : Scheme.{u}} (f₁ : A₁ ⟶ S) (g₁ : X₁ ⟶ S) (ι : S' ⟶ S)
    (f : A ⟶ S') (g : U ⟶ S') (a : A ⟶ A₁) (u : U ⟶ X₁)
    (ha : IsPullback a f f₁ ι) (hu : IsPullback u g g₁ ι) :
    IsPullback (pullback.map f g f₁ g₁ a u ι ha.w.symm hu.w.symm)
      (pullback.fst f g ≫ f) (pullback.fst f₁ g₁ ≫ f₁) ι := by

  have h1 : IsPullback (pullback.map f g f₁ g₁ a u ι ha.w.symm hu.w.symm) (pullback.snd f g) (pullback.snd f₁ g₁) u := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f₁ g₁) (v₁₃ := f₁) (h₂₂ := g₁) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f₁ g₁)
    rw [pullback.lift_fst, hu.w]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback f g) ha

  have h2 := IsPullback.paste_vert h1 hu
  rw [pullback.condition (f := f) (g := g), pullback.condition (f := f₁) (g := g₁)]
  exact h2
