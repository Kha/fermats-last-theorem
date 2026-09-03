import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_ball_eq_integral_smul_circleMap

theorem Complex.integral_ball_eq_integral_smul_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    ∫ z in Metric.ball c R, f z
      = ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, p.1 • f (circleMap c p.1 p.2) := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_ball_eq_integral_smul_circleMap.solution
