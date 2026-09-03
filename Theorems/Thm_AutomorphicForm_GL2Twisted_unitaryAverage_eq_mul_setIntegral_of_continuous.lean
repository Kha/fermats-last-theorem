import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_unitaryAverage_eq_mul_setIntegral_of_continuous

set_option autoImplicit false

open MeasureTheory AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.unitaryAverage_eq_mul_setIntegral_of_continuous
    (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) :
    unitaryAverage F = (1 / (2 * Real.pi ^ 3) : ℂ) *
      ∫ r in (Set.Ioo 0 Real.pi ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ (Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi)),
        (Real.sin r.1.2 * Real.cos r.1.2 : ℂ) * F (unitaryElt r.1.1 r.1.2 r.2.1 r.2.2) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_unitaryAverage_eq_mul_setIntegral_of_continuous.solution
