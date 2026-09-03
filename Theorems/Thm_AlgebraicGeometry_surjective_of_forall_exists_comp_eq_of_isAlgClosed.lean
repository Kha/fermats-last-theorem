import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_surjective_of_forall_exists_comp_eq_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

theorem AlgebraicGeometry.surjective_of_forall_exists_comp_eq_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (h : ∀ y : Spec (CommRingCat.of K) ⟶ Y, y ≫ g = 𝟙 _ →
      ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = y) :
    Surjective f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_surjective_of_forall_exists_comp_eq_of_isAlgClosed.solution
