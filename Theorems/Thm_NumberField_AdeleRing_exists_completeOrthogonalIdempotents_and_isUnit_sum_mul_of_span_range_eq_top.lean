import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top
    (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (t : ι → AdeleRing (𝓞 K) K)
    (h : Ideal.span (Set.range t) = ⊤) :
    ∃ e : ι → AdeleRing (𝓞 K) K, CompleteOrthogonalIdempotents e ∧ IsUnit (∑ i, e i * t i) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top.solution
