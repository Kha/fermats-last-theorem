import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback
    {S S' A₁ X₁ A U : Scheme.{u}} (f₁ : A₁ ⟶ S) (g₁ : X₁ ⟶ S) (ι : S' ⟶ S)
    (f : A ⟶ S') (g : U ⟶ S') (a : A ⟶ A₁) (u : U ⟶ X₁)
    (ha : IsPullback a f f₁ ι) (hu : IsPullback u g g₁ ι) :
    IsPullback (pullback.map f g f₁ g₁ a u ι ha.w.symm hu.w.symm)
      (pullback.fst f g ≫ f) (pullback.fst f₁ g₁ ≫ f₁) ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback.solution
