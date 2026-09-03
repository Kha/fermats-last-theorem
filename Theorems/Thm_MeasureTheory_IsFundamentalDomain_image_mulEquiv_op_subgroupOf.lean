import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_IsFundamentalDomain_image_mulEquiv_op_subgroupOf

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

theorem MeasureTheory.IsFundamentalDomain.image_mulEquiv_op_subgroupOf
    {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableMul A] [MeasurableMul B]
    (e : A ≃* B) (he : Measurable e) (he' : Measurable e.symm)
    (H : Subgroup A) (H' : Subgroup B) (hH : ∀ a : A, e a ∈ H' ↔ a ∈ H)
    (μ : Measure A) (D : Set A) (hD : IsFundamentalDomain H.op D μ) :
    IsFundamentalDomain H'.op (e '' D) (μ.map e) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_IsFundamentalDomain_image_mulEquiv_op_subgroupOf.solution
