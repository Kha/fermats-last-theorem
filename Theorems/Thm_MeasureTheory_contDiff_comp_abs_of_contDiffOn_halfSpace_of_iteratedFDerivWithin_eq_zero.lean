import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_contDiff_comp_abs_of_contDiffOn_halfSpace_of_iteratedFDerivWithin_eq_zero

set_option autoImplicit false

theorem MeasureTheory.contDiff_comp_abs_of_contDiffOn_halfSpace_of_iteratedFDerivWithin_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (D : E × ℝ → F) (hD : ContDiffOn ℝ (⊤ : ℕ∞) D {p : E × ℝ | 0 ≤ p.2})
    (hflat : ∀ (n : ℕ) (e : E), iteratedFDerivWithin ℝ n D {p : E × ℝ | 0 ≤ p.2} (e, 0) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => D (p.1, |p.2|)) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_contDiff_comp_abs_of_contDiffOn_halfSpace_of_iteratedFDerivWithin_eq_zero.solution
