import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral

set_option autoImplicit false

open scoped FourierTransform

theorem MeasureTheory.tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral
    (h : ℝ → ℂ) (hh : MeasureTheory.Integrable h)
    (hFh : MeasureTheory.Integrable (𝓕 h)) (h0 : ContinuousAt h 0) :
    Filter.Tendsto (fun R : ℝ => ∫ t : ℝ, ((Real.sin (R * t) / t : ℝ) : ℂ) * h t)
      Filter.atTop (nhds ((Real.pi : ℂ) * h 0)) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral.solution
