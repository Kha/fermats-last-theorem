import Mathlib
import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_RSCarrier
import P2M.Util
import P2M.Sol.S_RSCarrier_integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq

set_option autoImplicit false

open MeasureTheory

theorem RSCarrier.integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (a : G) (ha : ∀ x : G, x ∈ H ↔ a * x * a⁻¹ ∈ H)
    (haμ : ∀ φ : H → ENNReal, Measurable φ →
      ∫⁻ x : H, φ ⟨a * (x : G) * a⁻¹, (ha (x : G)).1 x.2⟩ ∂μH = ∫⁻ x : H, φ x ∂μH)
    (δ : G → ℝ) (hδH : ∀ h ∈ H, ∀ g : G, δ (h * g) = δ g) (hδa : ∀ g : G, δ (a * g) = δ g)
    (s : ℂ) (W F : G → ℂ)
    (hWF : ∀ h ∈ H, ∀ g : G, W (h * g) * F (h * g) = W g * F g)
    (hmeas : Measurable (fun g : G => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)))
    (hint : Integrable (fun g : G => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (HaarQuotient.density H μH))) :
    Integrable (fun g : G => (W (a * g) * F (a * g)) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity (HaarQuotient.density H μH)) ∧
      RSCarrier.rsLocalIntegral μ H μH δ s (fun g => W (a * g)) (fun g => F (a * g)) =
        RSCarrier.rsLocalIntegral μ H μH δ s W F := by p2m_exact_reverting @_root_.P2MW.S_RSCarrier_integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq.solution
