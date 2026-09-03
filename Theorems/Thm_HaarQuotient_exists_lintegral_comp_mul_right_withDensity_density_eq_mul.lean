import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_exists_lintegral_comp_mul_right_withDensity_density_eq_mul

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal Pointwise

theorem HaarQuotient.exists_lintegral_comp_mul_right_withDensity_density_eq_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (x : G) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → ℝ≥0∞), Measurable Φ → (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      ∫⁻ g, Φ (g * x) ∂(μ.withDensity (HaarQuotient.density H μH)) =
        c * ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_exists_lintegral_comp_mul_right_withDensity_density_eq_mul.solution
