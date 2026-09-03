import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ W : G → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable W ∧ HasCompactSupport W ∧ (∃ B : ℝ, ∀ x, W x ≤ B) ∧
      ∀ x : G, (∃ t : T, ∃ k ∈ Ω, x = (t : G) * k) → ∫ t : T, W ((t : G) * x) ∂τ = 1 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact.solution
