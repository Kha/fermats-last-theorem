import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.Index
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (H H' : Subgroup G) (hle : H ≤ H') (hH : MeasurableSet (H : Set G)) (hfin : H.relIndex H' ≠ 0) :
    μ (H' : Set G) = (H.relIndex H' : ENNReal) * μ (H : Set G) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant.solution
