import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_contDiffOn_integral_mul_log_sq_add_sq_halfSpace

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.contDiffOn_integral_mul_log_sq_add_sq_halfSpace
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : E × ℝ => ∫ s : ℝ, g (p.1, s) * (Real.log (s ^ 2 + p.2 ^ 2) : ℂ))
      {p : E × ℝ | 0 ≤ p.2} := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_contDiffOn_integral_mul_log_sq_add_sq_halfSpace.solution
