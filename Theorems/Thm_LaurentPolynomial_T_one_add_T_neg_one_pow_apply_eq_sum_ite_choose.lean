import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentPolynomial_T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose

set_option autoImplicit false

theorem LaurentPolynomial.T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose
    (R : Type*) [CommSemiring R] (k : ℕ) (m : ℤ) :
    ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial R).coeff m =
      ∑ i ∈ Finset.range (k + 1), if (2 * (i : ℤ) - k = m) then ((k.choose i : ℕ) : R) else 0 := by p2m_exact_reverting @_root_.P2MW.S_LaurentPolynomial_T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose.solution
