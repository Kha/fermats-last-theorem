import Mathlib
import P2M.Util
import P2M.Sol.S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm

theorem AnalyticOnNhd.log_norm_le_circleAverage_log_norm {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R := by p2m_exact_reverting @_root_.P2MW.S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm.solution
