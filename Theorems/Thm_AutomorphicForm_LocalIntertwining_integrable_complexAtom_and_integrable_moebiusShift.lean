import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (_habm : a₀ + b₀ ≤ m) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℂ → ℂ := fun σ z =>
      z ^ a₀ * (starRingEnd ℂ) z ^ b₀ * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)
    Integrable (atom σ) ∧
    Integrable (fun z : ℂ =>
      (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + z * d) / (a + z * c))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift.solution
