import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsFinite.of_isFinite_comp_of_surjective_of_isProper
    {X₀ X Y : Scheme.{u}} (i : X₀ ⟶ X) [Surjective i] (g : X ⟶ Y) [IsProper g] [IsFinite (i ≫ g)] :
    IsFinite g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper.solution
