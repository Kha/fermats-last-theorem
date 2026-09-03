import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

theorem MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    {E C : Set G} (hC : IsCompact C) (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul.solution
