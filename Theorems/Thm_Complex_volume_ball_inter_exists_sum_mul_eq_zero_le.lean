import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le

open MeasureTheory Metric
theorem Complex.volume_ball_inter_exists_sum_mul_eq_zero_le {n : ℕ} (c : ℂ → Fin n → ℂ) (z₀ : ℂ) (K : Set ℂ)
    (hc : c z₀ ≠ 0) {δ : ℝ} (hδ : ∀ z ∈ K, ‖c z - c z₀‖ ≤ δ) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ K, ∑ j, b j * c z j = 0}
      ≤ ENNReal.ofReal ((n * δ / ‖c z₀‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1) := by p2m_exact_reverting @_root_.P2MW.S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le.solution
