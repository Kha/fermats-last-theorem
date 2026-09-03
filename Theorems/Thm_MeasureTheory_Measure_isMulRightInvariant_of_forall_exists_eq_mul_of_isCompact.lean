import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    (Z C : Set G) (hZ : ∀ z ∈ Z, ∀ g : G, g * z = z * g)
    (hC : IsCompact C) (hcov : ∀ g : G, ∃ z ∈ Z, ∃ k ∈ C, g = z * k)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact.solution
