import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_range_subset_of_isLocalRing_of_closedPoint_mem

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.range_subset_of_isLocalRing_of_closedPoint_mem
    {X : Scheme.{u}} (U : X.Opens) (T : Type u) [CommRing T] [IsLocalRing T]
    (f : Spec (CommRingCat.of T) ⟶ X) (hx : f.base (IsLocalRing.closedPoint T) ∈ U) :
    Set.range f.base ⊆ (U : Set ↥X) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_range_subset_of_isLocalRing_of_closedPoint_mem.solution
