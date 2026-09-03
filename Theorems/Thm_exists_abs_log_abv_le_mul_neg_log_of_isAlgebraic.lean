import Mathlib
import P2M.Util
import P2M.Sol.S_exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic

set_option autoImplicit false

theorem exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic
    {K : Type*} [Field K] [CharZero K] (x : K) (hx0 : x ≠ 0) (hx : IsAlgebraic ℚ x)
    (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue K ℝ, IsNonarchimedean μ → μ (p : K) < 1 →
      |Real.log (μ x)| ≤ c * (-Real.log (μ (p : K))) := by p2m_exact_reverting @_root_.P2MW.S_exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic.solution
