import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_isClosed_of_forall_rationalPoint_mem_iff
    {κ : Type u} [Field κ] [IsAlgClosed κ] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f]
    {Z₁ Z₂ : Set Y} (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂)
    (h : ∀ y : Spec (CommRingCat.of κ) ⟶ Y, y ≫ f = 𝟙 _ →
      (y.base (IsLocalRing.closedPoint κ) ∈ Z₁ ↔ y.base (IsLocalRing.closedPoint κ) ∈ Z₂)) :
    Z₁ = Z₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff.solution
