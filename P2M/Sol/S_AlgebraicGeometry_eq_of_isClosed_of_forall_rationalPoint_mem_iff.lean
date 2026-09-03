import Mathlib
import Theorems.Thm_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f]
    {Z₁ Z₂ : Set Y} (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂)
    (h : ∀ y : Spec (CommRingCat.of κ) ⟶ Y, y ≫ f = 𝟙 _ →
      (y.base (IsLocalRing.closedPoint κ) ∈ Z₁ ↔ y.base (IsLocalRing.closedPoint κ) ∈ Z₂)) :
    Z₁ = Z₂ := by
  haveI : JacobsonSpace Y := AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType f

  have key : Z₁ ∩ closedPoints Y = Z₂ ∩ closedPoints Y := by
    ext x
    simp only [Set.mem_inter_iff, mem_closedPoints_iff]
    constructor
    · rintro ⟨hx, hc⟩
      obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton κ f x hc
      have hw : z.left ≫ f = 𝟙 _ := by simpa using Over.w z
      exact ⟨by rw [← hz]; exact (h z.left hw).mp (hz ▸ hx), hc⟩
    · rintro ⟨hx, hc⟩
      obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton κ f x hc
      have hw : z.left ≫ f = 𝟙 _ := by simpa using Over.w z
      exact ⟨by rw [← hz]; exact (h z.left hw).mpr (hz ▸ hx), hc⟩
  rw [← closure_inter_closedPoints h₁, ← closure_inter_closedPoints h₂, key]
