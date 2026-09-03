import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Surjective f] [QuasiCompact f]
    [Smooth (f ≫ g)] : Smooth g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective.solution
