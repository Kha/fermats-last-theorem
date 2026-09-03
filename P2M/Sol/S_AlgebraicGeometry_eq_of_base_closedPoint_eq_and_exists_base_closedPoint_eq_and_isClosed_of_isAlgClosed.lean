import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f] :
    (∀ (y y' : Spec (CommRingCat.of κ) ⟶ Y), y ≫ f = 𝟙 _ → y' ≫ f = 𝟙 _ →
        y.base (IsLocalRing.closedPoint κ) = y'.base (IsLocalRing.closedPoint κ) → y = y') ∧
    (∀ q : Y, IsClosed ({q} : Set Y) →
        ∃ y : Spec (CommRingCat.of κ) ⟶ Y, y ≫ f = 𝟙 _ ∧ y.base (IsLocalRing.closedPoint κ) = q) ∧
    (Finite Y → ∀ q : Y, IsClosed ({q} : Set Y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y y' hy hy' h
    exact ext_of_apply_closedPoint_eq f hy hy' h
  · intro q hq
    exact ⟨pointOfClosedPoint f q hq, pointOfClosedPoint_comp f q hq,
      pointOfClosedPoint_apply f q hq _⟩
  · intro hY q
    haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
    haveI : Finite Y := hY
    exact isClosed_discrete _
