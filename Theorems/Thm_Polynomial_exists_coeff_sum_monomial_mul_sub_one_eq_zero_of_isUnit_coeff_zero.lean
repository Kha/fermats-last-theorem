import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero
set_option autoImplicit false

theorem Polynomial.exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero
    {A : Type*} [CommRing A] (s : Polynomial A) (hs : IsUnit (s.coeff 0)) (m : ℕ) :
    ∃ σ : Fin (m + 1) → A,
      ∀ r : Fin (m + 1), ((∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (σ r')) * s - 1).coeff r = 0 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero.solution
