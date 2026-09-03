import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [IsSeparated f]
    (S : Finset X) (hS : ∀ x ∈ S, IsDiscreteValuationRing (X.presheaf.stalk x)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk.solution
