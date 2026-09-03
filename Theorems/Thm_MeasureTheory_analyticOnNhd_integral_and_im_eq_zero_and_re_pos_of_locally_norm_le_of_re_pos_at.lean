import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y)
    (a : ℝ) (F : ℂ → Y → ℂ)
    (hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ)
    (hhol : ∀ y : Y, Differentiable ℂ (fun s => F s y))
    (hdom : ∀ s₀ : ℂ, a < s₀.re → ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M μ ∧
      ∀ s ∈ Metric.ball s₀ ε, ∀ y : Y, ‖F s y‖ ≤ M y)
    (hreal : ∀ σ : ℝ, a < σ → ∀ y : Y, (F σ y).im = 0 ∧ 0 ≤ (F σ y).re)
    (hcont : ∀ σ : ℝ, a < σ → Continuous (F σ))
    (y₀ : Y) (hpt : ∀ σ : ℝ, a < σ → 0 < (F σ y₀).re)
    (hopen : ∀ U : Set Y, IsOpen U → y₀ ∈ U → 0 < μ U) :
    (∀ s : ℂ, a < s.re → Integrable (F s) μ) ∧
      AnalyticOnNhd ℂ (fun s : ℂ => ∫ y, F s y ∂μ) {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ → (∫ y, F σ y ∂μ).im = 0 ∧ 0 < (∫ y, F σ y ∂μ).re) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at.solution
