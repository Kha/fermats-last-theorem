import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_finrank_eq_of_isPullback_of_irreducibleSpace

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.finrank_eq_of_isPullback_of_irreducibleSpace
    {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] [IrreducibleSpace Y]
    (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (h : IsPullback g' π' π g) [Nonempty Y'] (d : ℕ)
    (hd : ∀ y' : Y', π'.finrank y' = d) (y : Y) : π.finrank y = d := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_eq_of_isPullback_of_irreducibleSpace.solution
