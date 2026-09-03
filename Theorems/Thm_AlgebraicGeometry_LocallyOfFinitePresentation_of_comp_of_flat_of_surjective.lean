import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_flat_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    [QuasiCompact f] [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_flat_of_surjective.solution
