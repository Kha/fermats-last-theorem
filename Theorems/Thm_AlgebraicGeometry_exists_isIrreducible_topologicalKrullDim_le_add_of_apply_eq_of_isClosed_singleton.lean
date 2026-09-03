import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [IrreducibleSpace ↥X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (o : X ⟶ Y) (ho : o ≫ fY = fX) {y : ↥Y} (hy : IsClosed ({y} : Set ↥Y))
    {x : ↥X} (hx : o x = y) :
    ∃ Z : Set ↥X, x ∈ Z ∧ Z ⊆ o ⁻¹' {y} ∧ IsIrreducible Z ∧ IsClosed Z ∧
      topologicalKrullDim ↥X ≤
        topologicalKrullDim ↥Z + topologicalKrullDim ↥(closure (Set.range o)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton.solution
