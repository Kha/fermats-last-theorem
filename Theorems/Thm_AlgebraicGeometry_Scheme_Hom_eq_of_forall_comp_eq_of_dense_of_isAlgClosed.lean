import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isAlgClosed

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~dense_setOf_exists_section_of_isAlgClosed"

universe u

theorem AlgebraicGeometry.Scheme.Hom.eq_of_forall_comp_eq_of_dense_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {X Y S : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (F G : X ⟶ Y) (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (U : X.Opens) (hU : Dense (U : Set ↥X))
    (h : ∀ y : Spec (CommRingCat.of k) ⟶ X, y ≫ f = 𝟙 _ → y.base (IsLocalRing.closedPoint k) ∈ U →
      y ≫ F = y ≫ G) :
    F = G := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isAlgClosed.solution
