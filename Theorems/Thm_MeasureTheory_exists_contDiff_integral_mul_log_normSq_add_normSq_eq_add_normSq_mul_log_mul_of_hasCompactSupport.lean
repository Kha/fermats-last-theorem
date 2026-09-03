import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℂ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ A B : E × ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (e : E) (r : ℂ),
        ∫ z : ℂ, g (e, z) * (Real.log (‖z‖ ^ 2 + ‖r‖ ^ 2) : ℂ) =
          A (e, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B (e, r) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport.solution
