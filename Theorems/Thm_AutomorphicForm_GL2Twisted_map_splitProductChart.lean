import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_map_splitProductChart
set_option autoImplicit false
open MeasureTheory

theorem AutomorphicForm.GL2Twisted.map_splitProductChart :
    Measure.map
      (fun p : Fin 2 → Fin 2 → ℂ => Matrix.of.symm
      (((if h : 0 < (p 1 0).re ∧ 0 < (p 1 0).im then
            twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2) ((p 1 0).re * p 1 1) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
              unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im
          else 1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))
      ((volume.restrict
        {p : Fin 2 → Fin 2 → ℂ |
          0 < (p 1 0).re ∧ 0 < (p 1 0).im ∧
          0 < (p 0 0).re ∧ (p 0 0).re < Real.pi ∧ 0 < (p 0 0).im ∧ (p 0 0).im < Real.pi / 2 ∧
          0 < (p 0 1).re ∧ (p 0 1).re < 2 * Real.pi ∧ 0 < (p 0 1).im ∧ (p 0 1).im < 2 * Real.pi}).withDensity
        (fun p : Fin 2 → Fin 2 → ℂ =>
          ENNReal.ofReal (2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im))) =
      volume.restrict {m : Fin 2 → Fin 2 → ℂ | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0} := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_map_splitProductChart.solution
