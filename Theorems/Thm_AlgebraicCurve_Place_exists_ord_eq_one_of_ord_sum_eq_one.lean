import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Place.exists_ord_eq_one_of_ord_sum_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → F)
    (hf : ∀ i ∈ s, f i = 0 ∨ 1 ≤ v.ord (f i))
    (h : v.ord (∑ i ∈ s, algebraMap K F (c i) * f i) = 1) :
    ∃ i ∈ s, v.ord (f i) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one.solution
