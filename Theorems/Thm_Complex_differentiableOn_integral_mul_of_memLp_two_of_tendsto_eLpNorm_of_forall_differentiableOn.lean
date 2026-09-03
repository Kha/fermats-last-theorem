import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn

set_option autoImplicit false

theorem Complex.differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn
    {Y : Type*} [MeasurableSpace Y] (μ : MeasureTheory.Measure Y) [MeasureTheory.SFinite μ]
    {U : Set ℂ} (hU : IsOpen U)
    (v : ℂ → Y → ℂ) (w : Y → ℂ)
    (hw : MeasureTheory.MemLp w 2 μ)
    (hvm : ∀ z ∈ U, Measurable (v z))
    (hv : ∀ z ∈ U, MeasureTheory.MemLp (v z) 2 μ)
    (hvc : ∀ z₀ ∈ U, Filter.Tendsto (fun z => MeasureTheory.eLpNorm (v z - v z₀) 2 μ)
      (nhdsWithin z₀ U) (nhds 0))
    (hhol : ∀ y : Y, DifferentiableOn ℂ (fun z => v z y) U) :
    DifferentiableOn ℂ (fun z => ∫ y, v z y * w y ∂μ) U := by p2m_exact_reverting @_root_.P2MW.S_Complex_differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn.solution
