import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal Pointwise

theorem HaarQuotient.exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (x : G) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → E), Measurable Φ → (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      (Integrable (fun g => Φ (g * x)) (μ.withDensity (HaarQuotient.density H μH)) ↔
        Integrable Φ (μ.withDensity (HaarQuotient.density H μH))) ∧
      (∫ g, Φ (g * x) ∂(μ.withDensity (HaarQuotient.density H μH))) =
        (c : ℝ) • ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul.solution
