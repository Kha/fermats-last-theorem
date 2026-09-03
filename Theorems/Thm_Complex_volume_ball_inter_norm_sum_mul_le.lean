import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_volume_ball_inter_norm_sum_mul_le

open MeasureTheory Metric
theorem Complex.volume_ball_inter_norm_sum_mul_le {n : ℕ} (w : Fin n → ℂ) (hw : w ≠ 0) (ε : ℝ) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ‖∑ j, b j * w j‖ ≤ ε}
      ≤ ENNReal.ofReal ((ε / ‖w‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1) := by p2m_exact_reverting @_root_.P2MW.S_Complex_volume_ball_inter_norm_sum_mul_le.solution
