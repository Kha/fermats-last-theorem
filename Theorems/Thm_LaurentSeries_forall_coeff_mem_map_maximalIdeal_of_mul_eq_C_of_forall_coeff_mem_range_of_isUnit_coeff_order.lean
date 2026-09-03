import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_forall_coeff_mem_map_maximalIdeal_of_mul_eq_C_of_forall_coeff_mem_range_of_isUnit_coeff_order

set_option autoImplicit false

theorem LaurentSeries.forall_coeff_mem_map_maximalIdeal_of_mul_eq_C_of_forall_coeff_mem_range_of_isUnit_coeff_order
    (A L : Type) [CommRing A] [Field L] [Algebra A L] (hinj : Function.Injective (algebraMap A L))
    (I : Ideal A)
    (Y Z : LaurentSeries L) (n₀ : ℤ) (c : A)
    (hZA : ∀ n : ℤ, ∃ a : A, Z.coeff n = algebraMap A L a)
    (hZ0 : ∀ n : ℤ, n < n₀ → Z.coeff n = 0)
    (hZu : ∃ u : A, IsUnit u ∧ Z.coeff n₀ = algebraMap A L u)
    (hYZ : Y * Z = HahnSeries.C (algebraMap A L c))
    (hc : c ∈ I) :
    ∀ n : ℤ, ∃ a ∈ I, Y.coeff n = algebraMap A L a := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_forall_coeff_mem_map_maximalIdeal_of_mul_eq_C_of_forall_coeff_mem_range_of_isUnit_coeff_order.solution
