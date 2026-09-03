import Mathlib
import P2M.Util
import P2M.Sol.S_AnalyticOnNhd_log_norm_sub_mul_le_setAverage_ball

theorem AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball {F : ℂ → ℂ} {g : ℂ → ℝ} {c : ℂ}
    {R k M : ℝ} (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R)) (hc : F c ≠ 0) (hR : 0 < R)
    (hg : ContinuousOn g (Metric.closedBall c R)) (hM : ∀ z ∈ Metric.closedBall c R, g z ≤ M)
    (hk : 0 ≤ k) :
    Real.log ‖F c‖ - k * M ≤ ⨍ z in Metric.ball c R, (Real.log ‖F z‖ - k * g z) := by p2m_exact_reverting @_root_.P2MW.S_AnalyticOnNhd_log_norm_sub_mul_le_setAverage_ball.solution
