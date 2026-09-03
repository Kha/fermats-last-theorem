import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq

theorem Complex.exists_analyticOnNhd_comp_pow_of_forall_mul_eq {e : ℕ} (he : 0 < e) {ω : ℂ} (hω : IsPrimitiveRoot ω e)
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r))
    (hinv : ∀ z ∈ Metric.ball 0 r, f (ω * z) = f z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 (r ^ e)) ∧ ∀ z ∈ Metric.ball 0 r, f z = F (z ^ e) := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq.solution
