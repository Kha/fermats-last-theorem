import Mathlib
import P2M.Util
import P2M.Sol.S_RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq

set_option autoImplicit false

open Polynomial

theorem RatFunc.X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq
    (N : ℕ) (hN : 1 < N) (σ : ℝ) (f : ℂ → ℂ)
    (P Q P' Q' : Polynomial ℂ) (m m' : ℤ) (hQ : Q ≠ 0) (hQ' : Q' ≠ 0)
    (h : ∀ s : ℂ, σ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)))
    (h' : ∀ s : ℂ, σ < s.re → f s * Q'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s))) :
    (RatFunc.X : RatFunc ℂ) ^ (-m) * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) =
      (RatFunc.X : RatFunc ℂ) ^ (-m') * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P' / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q') := by p2m_exact_reverting @_root_.P2MW.S_RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq.solution
