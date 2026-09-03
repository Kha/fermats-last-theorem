import Mathlib
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

theorem MeasureTheory.Measure.exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (Set.range f))
    (N : Subgroup G) (hN : ∀ x : G, x ∈ N ↔ f x = 1)
    (μN : Measure N) [μN.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map (fun q : MulAction.orbitRel.Quotient N G => f q.out) (HaarQuotient.measure μ N μN) =
        ENNReal.ofReal κ • ν.restrict (Set.range f) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range.solution
