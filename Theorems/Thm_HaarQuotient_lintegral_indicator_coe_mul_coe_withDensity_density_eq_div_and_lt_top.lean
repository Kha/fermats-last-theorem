import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal Pointwise

theorem HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    ∫⁻ g, ((H : Set G) * (K : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g ∂(μ.withDensity (HaarQuotient.density H μH)) =
        μ K / μH (((↑) : H → G) ⁻¹' (K : Set G)) ∧
      ∫⁻ g, ((H : Set G) * (K : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g ∂(μ.withDensity (HaarQuotient.density H μH)) < ⊤ := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top.solution
