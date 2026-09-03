import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    IsOpen (irreducibleComponent x) ∧ ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = irreducibleComponent x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk.solution
