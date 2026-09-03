import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isSeparated_of_isFinite_of_surjective_of_comp_eq
    {X Y S : Scheme.{0}} (p : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (h : p ≫ g = f)
    [IsFinite p] [Surjective p] [IsSeparated f] : IsSeparated g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq.solution
