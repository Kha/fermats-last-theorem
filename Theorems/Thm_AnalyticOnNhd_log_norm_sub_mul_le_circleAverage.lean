import Mathlib
import P2M.Util
import P2M.Sol.S_AnalyticOnNhd_log_norm_sub_mul_le_circleAverage

theorem AnalyticOnNhd.log_norm_sub_mul_le_circleAverage {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) {g : ℂ → ℝ} {k M : ℝ}
    (hg : CircleIntegrable g c R) (hM : ∀ z ∈ Metric.sphere c |R|, g z ≤ M) (hk : 0 ≤ k) :
    Real.log ‖F c‖ - k * M ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖ - k * g z) c R := by p2m_exact_reverting @_root_.P2MW.S_AnalyticOnNhd_log_norm_sub_mul_le_circleAverage.solution
