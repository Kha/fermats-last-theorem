import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import P2M.Util
import P2M.Sol.S_EisensteinGeneral_Arch_exists_realKType

open Set MeasureTheory
set_option autoImplicit false

theorem EisensteinGeneral.Arch.exists_realKType (k : ℤ) :
    ∃ J : ℂ → ℝ → ℂ,
      (∀ t : ℝ, t ≠ 0 → Differentiable ℂ (fun w : ℂ => J w t)) ∧
      (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 →
        J w t = ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w : ℂ) (t : ℝ), ‖w‖ ≤ R → t ≠ 0 →
        ‖J w t‖ ≤ C * max 1 (|t| ^ (-(N : ℝ))) * Real.exp (-c' * |t|)) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinGeneral_Arch_exists_realKType.solution
