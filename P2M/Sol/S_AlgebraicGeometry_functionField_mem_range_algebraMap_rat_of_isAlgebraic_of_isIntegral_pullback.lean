import Mathlib
import Theorems.Thm_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isDomain_functionField_tensorProduct_of_isIntegral_pullback
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) [IsIntegral X] (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hC : IsIntegral (CategoryTheory.Limits.pullback πX sC)) :
    ∃ hchar : CharZero X.functionField, haveI := hchar;
      ∀ x : X.functionField, IsAlgebraic ℚ x → x ∈ Set.range (algebraMap ℚ X.functionField) := by
  obtain ⟨hchar, hdom⟩ := AlgebraicGeometry.isDomain_functionField_tensorProduct_of_isIntegral_pullback M X πX C sC hC
  refine ⟨hchar, ?_⟩
  intro x hx
  exact IsAlgebraic.mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed X.functionField C hdom x hx
