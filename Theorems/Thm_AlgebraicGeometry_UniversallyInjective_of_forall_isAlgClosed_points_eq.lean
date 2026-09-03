import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_UniversallyInjective_of_forall_isAlgClosed_points_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.UniversallyInjective.of_forall_isAlgClosed_points_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x y : Spec (CommRingCat.of K) ⟶ X),
      x ≫ f = y ≫ f → x = y) :
    UniversallyInjective f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_UniversallyInjective_of_forall_isAlgClosed_points_eq.solution
