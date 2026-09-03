import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_abv_eval_sub_eval_le_mul_iSup

set_option autoImplicit false

theorem MvPolynomial.abv_eval_sub_eval_le_mul_iSup
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {r : ℕ} (G : MvPolynomial (Fin r) K) (C : ℝ) (hC : ∀ m, μ (G.coeff m) ≤ C)
    (x v : Fin r → K) (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    μ (MvPolynomial.eval x G - MvPolynomial.eval v G) ≤ C * ⨆ l, μ (x l - v l) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_abv_eval_sub_eval_le_mul_iSup.solution
