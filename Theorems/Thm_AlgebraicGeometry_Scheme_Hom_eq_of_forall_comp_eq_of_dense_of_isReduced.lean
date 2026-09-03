import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.eq_of_forall_comp_eq_of_dense_of_isReduced
    {X Y S : Scheme.{u}} [IsReduced X]
    (F G : X ⟶ Y) (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (D : Set ↥X) (hD : Dense D)
    (h : ∀ x ∈ D, ∃ (k : Type u) (_ : Field k) (y : Spec (CommRingCat.of k) ⟶ X),
      x ∈ Set.range y.base ∧ y ≫ F = y ≫ G) :
    F = G := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced.solution
