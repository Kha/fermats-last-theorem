import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isFinite_of_finite_setOf_exists_section_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hfin : {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x}.Finite) :
    IsFinite f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed.solution
