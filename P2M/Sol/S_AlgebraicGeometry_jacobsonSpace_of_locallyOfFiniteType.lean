import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] :
    JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace t
