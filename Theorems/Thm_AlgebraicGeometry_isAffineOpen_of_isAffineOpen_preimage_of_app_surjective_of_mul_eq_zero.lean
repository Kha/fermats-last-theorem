import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero
    {X X' : Scheme.{u}} (i : X ⟶ X') [Surjective i]
    (hsq : ∀ (V : X'.Opens), IsAffineOpen V → ∀ a b : Γ(X', V), (i.app V).hom a = 0 → (i.app V).hom b = 0 → a * b = 0)
    (U : X'.Opens) (hU : IsAffineOpen (i ⁻¹ᵁ U)) (hsurj : Function.Surjective (i.app U).hom) : IsAffineOpen U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero.solution
