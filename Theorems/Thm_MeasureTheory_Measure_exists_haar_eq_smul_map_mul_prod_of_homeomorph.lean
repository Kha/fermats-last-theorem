import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.Measure.exists_haar_eq_smul_map_mul_prod_of_homeomorph
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T S : Subgroup G) [MeasurableSpace T] [BorelSpace T] [MeasurableSpace S] [BorelSpace S]
    (e : T × S ≃ₜ G) (he : ∀ p : T × S, e p = (p.1 : G) * (p.2 : G))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (τ : Measure T) [τ.IsHaarMeasure]
    (ν : Measure S) [IsFiniteMeasureOnCompacts ν] [ν.IsMulRightInvariant] [ν.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • Measure.map e (τ.prod ν) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph.solution
