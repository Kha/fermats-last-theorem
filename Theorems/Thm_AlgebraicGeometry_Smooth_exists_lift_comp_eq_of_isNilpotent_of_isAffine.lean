import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isNilpotent_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [Smooth f]
    {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    (t : Spec (CommRingCat.of C) ⟶ S) (x₀ : Spec (CommRingCat.of (C ⧸ J)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ t) :
    ∃ x : Spec (CommRingCat.of C) ⟶ X, x ≫ f = t ∧ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ x = x₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine.solution
