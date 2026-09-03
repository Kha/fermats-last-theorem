import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType
    {R : Type u} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType πY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyR : πY y = IsLocalRing.closedPoint R) :
    Finite (IsLocalRing.ResidueField (Y.presheaf.stalk y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType.solution
