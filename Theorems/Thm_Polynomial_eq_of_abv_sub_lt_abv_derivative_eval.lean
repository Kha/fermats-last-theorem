import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_eq_of_abv_sub_lt_abv_derivative_eval

set_option autoImplicit false

open Polynomial

theorem Polynomial.eq_of_abv_sub_lt_abv_derivative_eval
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (g : Polynomial K) (hg : ∀ i, μ (g.coeff i) ≤ 1) {a b : K} (ha : μ a ≤ 1) (hb : μ b ≤ 1)
    (hga : g.eval a = 0) (hgb : g.eval b = 0)
    (hlt : μ (a - b) < μ ((Polynomial.derivative g).eval a)) : a = b := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_eq_of_abv_sub_lt_abv_derivative_eval.solution
