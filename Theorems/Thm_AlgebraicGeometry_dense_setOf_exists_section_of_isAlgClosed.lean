import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    Dense {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed.solution
