import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half
    (c' d' : ℂ) (_h : c' ≠ 0 ∨ d' ≠ 0) (a b m : ℕ) (_habm : a + b ≤ m) :
    Tendsto (fun σ : ℝ =>
        ∫ z : ℂ, ((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ)
          * (z ^ a * (starRingEnd ℂ) z ^ b
              * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.solution
