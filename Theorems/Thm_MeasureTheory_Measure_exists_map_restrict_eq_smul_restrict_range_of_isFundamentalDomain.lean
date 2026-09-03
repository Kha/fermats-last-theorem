import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

theorem MeasureTheory.Measure.exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (Set.range f))
    (Γ : Subgroup G) [Countable Γ] (hΓ : Γ ≤ f.ker)
    (hker : ∃ D : Set G, IsCompact D ∧ (f.ker : Set G) ⊆ (Γ : Set G) * D)
    (Θ : Set G) (hΘ : IsFundamentalDomain Γ Θ μ) :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map f (μ.restrict Θ) = ENNReal.ofReal κ • ν.restrict (Set.range f) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain.solution
