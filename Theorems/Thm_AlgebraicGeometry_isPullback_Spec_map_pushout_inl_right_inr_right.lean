import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPullback_Spec_map_pushout_inl_right_inr_right

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isPullback_Spec_map_pushout_inl_right_inr_right
    {R : Type u} [CommRing R] {B B₁ B₂ : Under (CommRingCat.of R)} (φ₁ : B ⟶ B₁) (φ₂ : B ⟶ B₂) :
    IsPullback (Spec.map (pushout.inl φ₁ φ₂).right) (Spec.map (pushout.inr φ₁ φ₂).right)
      (Spec.map φ₁.right) (Spec.map φ₂.right) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPullback_Spec_map_pushout_inl_right_inr_right.solution
