import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_abv_eval_div_sub_eval_div_le

set_option autoImplicit false

theorem MvPolynomial.abv_eval_div_sub_eval_div_le
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {r : ℕ} (A B : MvPolynomial (Fin r) K) (CA CB : ℝ)
    (hA : ∀ m, μ (A.coeff m) ≤ CA) (hB : ∀ m, μ (B.coeff m) ≤ CB)
    (x v : Fin r → K) (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1)
    (hBv : MvPolynomial.eval v B ≠ 0)
    (hclose : CB * (⨆ l, μ (x l - v l)) < μ (MvPolynomial.eval v B)) :
    μ (MvPolynomial.eval x B) = μ (MvPolynomial.eval v B) ∧
      μ (MvPolynomial.eval x A / MvPolynomial.eval x B - MvPolynomial.eval v A / MvPolynomial.eval v B)
        ≤ max (CA * μ (MvPolynomial.eval v B)) (CB * μ (MvPolynomial.eval v A)) / μ (MvPolynomial.eval v B) ^ 2
          * ⨆ l, μ (x l - v l) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_abv_eval_div_sub_eval_div_le.solution
