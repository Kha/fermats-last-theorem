import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative
set_option autoImplicit false

theorem Polynomial.exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative
    {A : Type*} [CommRing A] (F : Polynomial (Polynomial A)) (w₀ : A)
    (h0 : (F.eval (Polynomial.C w₀)).coeff 0 = 0)
    (hder : IsUnit ((F.derivative.eval (Polynomial.C w₀)).coeff 0)) (m : ℕ) :
    ∃ w : Fin (m + 1) → A, w 0 = w₀ ∧
      ∀ r : Fin (m + 1), (F.eval (∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (w r'))).coeff r = 0 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative.solution
