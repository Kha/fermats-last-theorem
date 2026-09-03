import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (O : Set ℂ) (hO : IsOpen O) (hO₀ : {s : ℂ | s.re = 0} ⊆ O)
    (N : ℂ → X → ℂ) (hNa : ∀ x : X, AnalyticOnNhd ℂ (fun s => N s x) O)
    (hNc : ContinuousOn (fun p : ℂ × X => N p.1 p.2) (O ×ˢ Set.univ))
    (t t' B : ℝ)
    (hB : ∀ τ ∈ Set.uIcc t t',
      ∫ x, ‖deriv (fun s : ℂ => N s x) ((τ : ℂ) * Complex.I)‖ ^ 2 ∂μ ≤ B ^ 2) :
    ∫ x, ‖N ((t : ℂ) * Complex.I) x - N ((t' : ℂ) * Complex.I) x‖ ^ 2 ∂μ ≤ (B * |t - t'|) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le.solution
