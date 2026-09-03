import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_RSCarrier
import P2M.Util
import P2M.Sol.S_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq

open MeasureTheory

theorem RSCarrier.rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (h : G) (hμh : Measure.map (· * h) μ = μ)
    (δ : G → ℝ) (hδ : Measurable δ) (hδpos : ∀ g : G, 0 < δ g) (hδmul : ∀ g k : G, δ (g * k) = δ g * δ k)
    (hδH : ∀ x ∈ H, ∀ g : G, δ (x * g) = δ g)
    (s : ℂ) (W F : G → ℂ) (hW : Measurable W) (hF : Measurable F)
    (hWF : ∀ x ∈ H, ∀ g k : G, W (x * g) * F (x * k) = W g * F k) :
    (Integrable (fun g : G => (W g * F (g * h)) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) (μ.withDensity (HaarQuotient.density H
      μH)) ↔ Integrable (fun g : G => (W (g * h⁻¹) * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) (μ.withDensity
      (HaarQuotient.density H μH))) ∧
      RSCarrier.rsLocalIntegral μ H μH δ s W (fun g => F (g * h)) = ((δ h⁻¹ : ℝ) : ℂ) ^ (s - 1 / 2) *
        RSCarrier.rsLocalIntegral μ H μH δ s (fun g => W (g * h⁻¹)) F := by p2m_exact_reverting @_root_.P2MW.S_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq.solution
