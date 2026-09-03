import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integrableOn_ball_iff_integrableOn_smul_circleMap

theorem Complex.integrableOn_ball_iff_integrableOn_smul_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    MeasureTheory.IntegrableOn f (Metric.ball c R) ↔
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (circleMap c p.1 p.2))
        (Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by p2m_exact_reverting @_root_.P2MW.S_Complex_integrableOn_ball_iff_integrableOn_smul_circleMap.solution
