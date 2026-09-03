import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero

set_option autoImplicit false

theorem Polynomial.exists_eval_mul_cpow_mul_eval_eq_of_ne_zero
    (q : ℂ) (hq : q ≠ 0) (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (hP : P ≠ 0) (hQd : Qd ≠ 0) :
    ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ s : ℂ,
        R₂.eval (q ^ s) * (q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s))) * Q.eval (q ^ s) =
          (R₁.eval (q ^ s) * q ^ ((r : ℂ) * s)) * (q ^ ((m : ℂ) * (-s)) * P.eval (q ^ s)) * Qd.eval (q ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero.solution
