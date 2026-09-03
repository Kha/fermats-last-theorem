import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_integral_comp_mulEquiv_withDensity_density_eq_of_involutive

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem HaarQuotient.integral_comp_mulEquiv_withDensity_density_eq_of_involutive
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μ : Measure G) [μ.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (φ : G ≃* G) (hφc : Continuous φ) (hφφ : ∀ g : G, φ (φ g) = g) (hφH : ∀ g : G, φ g ∈ H ↔ g ∈ H) :
    ∀ (Φ : G → E), (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      (∫ g, Φ (φ g) ∂(μ.withDensity (HaarQuotient.density H μH))) =
        ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_integral_comp_mulEquiv_withDensity_density_eq_of_involutive.solution
