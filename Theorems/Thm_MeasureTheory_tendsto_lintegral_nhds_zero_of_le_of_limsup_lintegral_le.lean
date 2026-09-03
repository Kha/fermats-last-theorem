import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import P2M.Util
import P2M.Sol.S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology

theorem MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F G : ι → α → ℝ≥0∞) (g : α → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) μ) (hG : ∀ i, AEMeasurable (G i) μ)
    (hFG : ∀ i, ∀ᵐ x ∂μ, F i x ≤ G i x)
    (hF0 : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0))
    (hGg : ∀ᵐ x ∂μ, Tendsto (fun i => G i x) l (𝓝 (g x)))
    (hg : ∫⁻ x, g x ∂μ ≠ ∞)
    (hlim : limsup (fun i => ∫⁻ x, G i x ∂μ) l ≤ ∫⁻ x, g x ∂μ) :
    Tendsto (fun i => ∫⁻ x, F i x ∂μ) l (𝓝 0) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le.solution
