import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact

set_option autoImplicit false

p2m_open "MeasureTheory~integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one~exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant"

theorem MeasureTheory.exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (C : Set G) (hC : IsCompact C) (hcov : ∀ g : G, ∃ t : T, ∃ k ∈ C, g = (t : G) * k) :
    ∃ κ : ℝ, 0 < κ ∧
      (∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Continuous w ∧ HasCompactSupport w ∧
        ∀ x : G, ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∀ w : G → ℝ, (∀ x, 0 ≤ w x) → Measurable w → HasCompactSupport w →
        (∀ x : G, ∫ t : T, w ((t : G) * x) ∂τ = 1) → ∫ x, w x ∂μ = κ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact.solution
