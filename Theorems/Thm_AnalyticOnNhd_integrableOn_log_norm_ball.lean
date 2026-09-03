import Mathlib
import P2M.Util
import P2M.Sol.S_AnalyticOnNhd_integrableOn_log_norm_ball

theorem AnalyticOnNhd.integrableOn_log_norm_ball {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R)) (hc : F c ≠ 0) :
    MeasureTheory.IntegrableOn (fun z ↦ Real.log ‖F z‖) (Metric.ball c R) := by p2m_exact_reverting @_root_.P2MW.S_AnalyticOnNhd_integrableOn_log_norm_ball.solution
