import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant]
    (s : Set G) (hs : μ s < ⊤) (T : Finset G) :
    μ (⋃ x ∈ T, (· * x) '' s) < ⊤ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top.solution
