import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ A B : E × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (e : E) (ρ : ℝ),
        ∫ s : ℝ, g (e, s) * (Real.log (s ^ 2 + ρ ^ 2) : ℂ) = A (e, ρ) + ((|ρ| : ℝ) : ℂ) * B (e, ρ) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport.solution
