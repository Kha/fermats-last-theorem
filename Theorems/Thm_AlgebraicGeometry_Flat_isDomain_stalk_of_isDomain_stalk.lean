import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Flat.isDomain_stalk_of_isDomain_stalk
    {Y Z : Scheme.{u}} (h : Y ⟶ Z) [Flat h] (y : Y) [IsDomain (Y.presheaf.stalk y)] :
    IsDomain (Z.presheaf.stalk (h y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk.solution
