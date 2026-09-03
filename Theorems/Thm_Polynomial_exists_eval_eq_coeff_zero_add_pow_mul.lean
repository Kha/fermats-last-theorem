import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Rat
import P2M.Util
import P2M.Sol.S_Polynomial_exists_eval_eq_coeff_zero_add_pow_mul

theorem Polynomial.exists_eval_eq_coeff_zero_add_pow_mul (p : Polynomial ℚ) (N : ℤ) (hN : N ≠ 0) (hden : ∀ k : ℕ, ∀ q : ℕ, q.Prime → q ∣ (p.coeff k).den → (q : ℤ) ∣ N) : ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ m : ℤ, ∃ z : ℤ, p.eval ((N : ℚ) ^ K * m) = p.coeff 0 + (N : ℚ) ^ (K - K₀) * z := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_eval_eq_coeff_zero_add_pow_mul.solution
