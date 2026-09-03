import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    {R : Type u} [CommRing R] {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
  refine IsPullback.of_right (h₁₂ := pullback.fst c t) (v₁₃ := c) (h₂₂ := t) ?_
    (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := ψ)) (IsPullback.of_hasPullback c t)
  rw [RelPicard.BaseChange.baseChangeSnd_fst' (cc := c) (ψ := ψ), ψ.2]
  exact IsPullback.of_hasPullback c t'
