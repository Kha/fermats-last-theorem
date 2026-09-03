import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem HaarQuotient.exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure]
    (μH μH' : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    [μH'.IsHaarMeasure] [μH'.IsMulRightInvariant] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → E), (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      (∫ g, Φ g ∂(μ'.withDensity (HaarQuotient.density H μH'))) =
        (c : ℝ) • ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure.solution
