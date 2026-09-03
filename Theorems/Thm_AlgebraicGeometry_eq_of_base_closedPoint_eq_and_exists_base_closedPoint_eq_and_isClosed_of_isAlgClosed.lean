import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
    (κ : Type u) [Field κ] [IsAlgClosed κ] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f] :
    (∀ (y y' : Spec (CommRingCat.of κ) ⟶ Y), y ≫ f = 𝟙 _ → y' ≫ f = 𝟙 _ →
        y.base (IsLocalRing.closedPoint κ) = y'.base (IsLocalRing.closedPoint κ) → y = y') ∧
    (∀ q : Y, IsClosed ({q} : Set Y) →
        ∃ y : Spec (CommRingCat.of κ) ⟶ Y, y ≫ f = 𝟙 _ ∧ y.base (IsLocalRing.closedPoint κ) = q) ∧
    (Finite Y → ∀ q : Y, IsClosed ({q} : Set Y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed.solution
