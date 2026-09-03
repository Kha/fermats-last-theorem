import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_ne_zero_map_mulEquiv_eq_smul_pi

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

theorem MeasureTheory.Measure.exists_ne_zero_map_mulEquiv_eq_smul_pi
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : ∀ i, Measure (H i)) [∀ i, (ν i).IsHaarMeasure]
    (Θ : G ≃* (∀ i, H i)) (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map Θ μ = c • Measure.pi ν := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_ne_zero_map_mulEquiv_eq_smul_pi.solution
