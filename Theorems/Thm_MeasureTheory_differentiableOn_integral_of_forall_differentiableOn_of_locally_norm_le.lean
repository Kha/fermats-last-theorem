import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le.solution
