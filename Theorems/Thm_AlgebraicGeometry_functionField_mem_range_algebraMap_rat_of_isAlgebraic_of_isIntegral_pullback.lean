import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) [IsIntegral X] (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hC : IsIntegral (CategoryTheory.Limits.pullback πX sC)) :
    ∃ hchar : CharZero X.functionField, haveI := hchar;
      ∀ x : X.functionField, IsAlgebraic ℚ x → x ∈ Set.range (algebraMap ℚ X.functionField) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback.solution
