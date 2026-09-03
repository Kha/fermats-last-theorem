import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_ball_eq_integral_smul_intervalIntegral_circleMap

theorem Complex.integral_ball_eq_integral_smul_intervalIntegral_circleMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : MeasureTheory.IntegrableOn f (Metric.ball c R)) :
    ∫ z in Metric.ball c R, f z = ∫ r in Set.Ioo 0 R, r • ∫ θ in 0..2 * Real.pi, f (circleMap c r θ) := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_ball_eq_integral_smul_intervalIntegral_circleMap.solution
