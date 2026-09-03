import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport

set_option autoImplicit false

open MeasureTheory Filter

theorem MeasureTheory.tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (w : X → ℝ) (hwm : Measurable w) (hwc : HasCompactSupport w) (hwb : ∃ B : ℝ, ∀ x, |w x| ≤ B)
    (Φ : ℝ → X → ℂ) (Φ₀ : X → ℂ)
    (hΦm : ∀ θ : ℝ, AEStronglyMeasurable (Φ θ) μ) (hΦ₀m : AEStronglyMeasurable Φ₀ μ)
    (hΦ₀b : ∃ B₀ : ℝ, ∀ x ∈ tsupport w, ‖Φ₀ x‖ ≤ B₀)
    (hunif : TendstoUniformlyOn Φ Φ₀ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (tsupport w)) :
    Tendsto (fun θ : ℝ => ∫ x, Φ θ x * (w x : ℂ) ∂μ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x, Φ₀ x * (w x : ℂ) ∂μ)) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport.solution
