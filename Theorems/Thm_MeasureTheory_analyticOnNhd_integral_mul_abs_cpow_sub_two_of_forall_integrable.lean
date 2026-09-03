import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.IsolatedZeros
import P2M.Util
import P2M.Sol.S_MeasureTheory_analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable
    (P : ℝ → ℝ) (x₀ : ℝ) (hP : Measurable P) (hP0 : ∀ y : ℝ, 0 ≤ P y)
    (hPint : ∀ σ : ℝ, x₀ < σ → Integrable (fun y : ℝ => P y * |y| ^ (σ - 2))) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) {s : ℂ | x₀ < s.re} ∧
    (∀ σ : ℝ, x₀ < σ →
      (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).im = 0 ∧
      0 ≤ (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).re) ∧
    ((¬ ∀ᵐ y : ℝ, P y = 0) → ∀ σ : ℝ, x₀ < σ →
      0 < (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).re) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable.solution
