import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn

set_option autoImplicit false

theorem Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U) {S : Set Y} (hS : IsCompact S)
    (F : ℂ → Y → ℂ) (hF : ContinuousOn (Function.uncurry F) (U ×ˢ Set.univ))
    (hFS : ∀ z ∈ U, ∀ a ∉ S, F z a = 0)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by p2m_exact_reverting @_root_.P2MW.S_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn.solution
