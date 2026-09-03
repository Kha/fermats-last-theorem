import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType
    {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] :
    JacobsonSpace X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType.solution
