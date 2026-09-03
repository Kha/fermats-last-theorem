import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume

open MeasureTheory Metric
open scoped ENNReal NNReal
theorem Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume {n : ℕ} (c : ℂ → Fin n → ℂ)
    (S : Set ℂ) {η L : ℝ} (hη : 0 < η) (hηc : ∀ z ∈ S, η ≤ ‖c z‖)
    (hLip : ∀ z ∈ S, ∃ δ > 0, ∀ y ∈ Metric.closedBall z δ, ‖c y - c z‖ ≤ L * ‖y - z‖) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ S, ∑ j, b j * c z j = 0}
      ≤ ENNReal.ofReal ((n * L / η) ^ 2 / Real.pi) * volume (Metric.ball (0 : Fin n → ℂ) 1) * volume S := by p2m_exact_reverting @_root_.P2MW.S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume.solution
