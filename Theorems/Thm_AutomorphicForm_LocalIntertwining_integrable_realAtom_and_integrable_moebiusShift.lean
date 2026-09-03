import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    Integrable (atom σ) ∧
    Integrable (fun x : ℝ =>
      (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + x * d) / (a + x * c))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift.solution
