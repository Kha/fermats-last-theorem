import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isDomain_functionField_tensorProduct_of_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.isDomain_functionField_tensorProduct_of_isIntegral_pullback
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) [IsIntegral X] (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hC : IsIntegral (CategoryTheory.Limits.pullback πX sC)) :
    ∃ hchar : CharZero X.functionField, haveI := hchar;
      IsDomain (X.functionField ⊗[ℚ] C) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isDomain_functionField_tensorProduct_of_isIntegral_pullback.solution
