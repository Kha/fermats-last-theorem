import Mathlib.MeasureTheory.Measure.Haar.Basic
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure

open MeasureTheory

theorem MeasureTheory.Measure.map_eq_self_of_involutive_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (θ : G ≃* G) (hθ : Continuous θ) (hθinv : ∀ g : G, θ (θ g) = g) :
    Measure.map θ μ = μ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure.solution
