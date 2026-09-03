import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible

set_option autoImplicit false

open Polynomial

theorem Polynomial.eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible
    (t n : ℤ) (P : Polynomial ℚ)
    (hirr : Irreducible (X ^ 2 + C (t : ℚ) * X + C (n : ℚ) : Polynomial ℚ))
    (hP : P.natDegree ≤ 4)
    (hPQ : P * P.comp (-X - C (t : ℚ)) = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 4)
    (hpos : ∃ m : ℤ, 0 < P.eval (m : ℚ)) :
    P = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible.solution
