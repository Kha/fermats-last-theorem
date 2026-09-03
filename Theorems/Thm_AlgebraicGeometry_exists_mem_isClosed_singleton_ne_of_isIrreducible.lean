import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_mem_isClosed_singleton_ne_of_isIrreducible
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z)
    (x : X) (hxZ : x ∈ Z) (hx : IsClosed ({x} : Set X)) (hne : Z ≠ {x}) :
    ∃ x' ∈ Z, IsClosed ({x'} : Set X) ∧ x' ≠ x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible.solution
