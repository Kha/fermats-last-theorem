import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t, z.left.base (IsLocalRing.closedPoint k) = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton.solution
