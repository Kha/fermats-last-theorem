import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant
    {T : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup T) (hS : IsClosed (S : Set T)) [MeasurableSpace S] [BorelSpace S]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (C : Set T) (hC : IsCompact C) (hSC : ∀ t : T, ∃ s : S, ∃ c ∈ C, t = (s : T) * c) :
    ∃ β : T → ℝ, Continuous β ∧ HasCompactSupport β ∧ (∀ t, 0 ≤ β t) ∧
      ∀ t : T, ∫ s : S, β ((s : T) * t) ∂τS = 1 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant.solution
