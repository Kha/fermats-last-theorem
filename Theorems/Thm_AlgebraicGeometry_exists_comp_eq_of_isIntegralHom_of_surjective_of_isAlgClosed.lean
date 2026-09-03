import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed
    {M X : Scheme.{u}} (π : M ⟶ X) [IsIntegralHom π] (hsurj : Function.Surjective π.base)
    (k : Type u) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ X) :
    ∃ x : Spec (CommRingCat.of k) ⟶ M, x ≫ π = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed.solution
