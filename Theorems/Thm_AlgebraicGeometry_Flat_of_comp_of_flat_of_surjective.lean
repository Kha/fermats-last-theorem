import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective {X U Y : Scheme.{u}} (c : X ⟶ U) [Flat c]
    [Surjective c] (p : U ⟶ Y) [Flat (c ≫ p)] : Flat p := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective.solution
