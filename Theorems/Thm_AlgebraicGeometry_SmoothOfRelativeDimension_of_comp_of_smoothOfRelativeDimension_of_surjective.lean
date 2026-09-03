import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective
    {X Y Z : Scheme.{u}} [Nonempty X] (f : X ⟶ Y) (g : Y ⟶ Z) (a b : ℕ)
    [SmoothOfRelativeDimension a (f ≫ g)] [SmoothOfRelativeDimension b f] [Surjective f] [Smooth g] :
    SmoothOfRelativeDimension (a - b) g ∧ b ≤ a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective.solution
