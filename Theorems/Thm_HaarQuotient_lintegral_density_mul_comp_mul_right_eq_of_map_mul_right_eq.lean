import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq

open MeasureTheory

theorem HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (f : G → ENNReal) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (h : G)
    (hμh : Measure.map (· * h) μ = μ) :
    ∫⁻ g, HaarQuotient.density H μH g * f (g * h) ∂μ = ∫⁻ g, HaarQuotient.density H μH g * f g ∂μ := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.solution
