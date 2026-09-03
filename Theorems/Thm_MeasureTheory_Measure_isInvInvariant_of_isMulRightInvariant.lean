import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant.solution
