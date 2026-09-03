import Mathlib
import P2M.Util
import P2M.Sol.S_RestrictedProduct_measurable_iff_forall_measurable_apply

set_option autoImplicit false

open MeasureTheory
open scoped RestrictedProduct

theorem RestrictedProduct.measurable_iff_forall_measurable_apply
    {ι : Type*} [Countable ι] {R : ι → Type*}
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    {A : (i : ι) → Set (R i)} (hA : ∀ i, MeasurableSet (A i))
    [MeasurableSpace (Πʳ i, [R i, A i])] [BorelSpace (Πʳ i, [R i, A i])]
    {X : Type*} [MeasurableSpace X] (f : X → Πʳ i, [R i, A i]) :
    Measurable f ↔ ∀ i, Measurable fun x => f x i := by p2m_exact_reverting @_root_.P2MW.S_RestrictedProduct_measurable_iff_forall_measurable_apply.solution
