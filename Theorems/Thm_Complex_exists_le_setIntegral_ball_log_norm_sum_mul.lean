import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_le_setIntegral_ball_log_norm_sum_mul

open MeasureTheory Metric Set

theorem Complex.exists_le_setIntegral_ball_log_norm_sum_mul {r : ℕ} {φ : ℂ → Fin r → ℂ} {z_c : ℂ} {R R' : ℝ}
    (hR : 0 < R) (hRR' : 3 * R < R') (hφ : ∀ j, DifferentiableOn ℂ (fun z ↦ φ z j) (Metric.ball z_c R'))
    (hnd : ∀ a : Fin r → ℂ, a ≠ 0 → ∃ z ∈ Metric.ball z_c R', ∑ j, a j * φ z j ≠ 0) :
    ∃ C : ℝ, ∀ a : Fin r → ℂ, ‖a‖ = 1 →
      IntegrableOn (fun z ↦ Real.log ‖∑ j, a j * φ z j‖) (Metric.ball z_c R) ∧
      C ≤ ∫ z in Metric.ball z_c R, Real.log ‖∑ j, a j * φ z j‖ := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_le_setIntegral_ball_log_norm_sum_mul.solution
