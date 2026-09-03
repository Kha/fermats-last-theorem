import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero

set_option autoImplicit false

open scoped TensorProduct

theorem MvPolynomial.exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero
    (B : Type*) [CommRing B] {m : ℕ} (c : Fin m → MvPolynomial (Fin m) B)
    (hc : ∑ j, c j * MvPolynomial.X j = 0) :
    ∃ e : Fin m → Fin m → MvPolynomial (Fin m) B,
      (∀ j k, e j k = -e k j) ∧ (∀ j, e j j = 0) ∧ ∀ j, c j = ∑ k, e j k * MvPolynomial.X k := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero.solution
