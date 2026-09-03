import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_forall_cpow_mul_eval_eq_of_forall_lt_re

theorem LanglandsTunnell.forall_cpow_mul_eval_eq_of_forall_lt_re
    (N : ℕ) (hN : 1 < N) (P Q : Polynomial ℂ) (m n : ℤ) (c : ℝ)
    (h : ∀ u : ℂ, c < u.re →
      (N : ℂ) ^ ((m : ℂ) * u) * P.eval ((N : ℂ) ^ (-u)) = (N : ℂ) ^ ((n : ℂ) * u) * Q.eval ((N : ℂ) ^ (-u))) :
    ∀ u : ℂ, (N : ℂ) ^ ((m : ℂ) * u) * P.eval ((N : ℂ) ^ (-u)) = (N : ℂ) ^ ((n : ℂ) * u) * Q.eval ((N : ℂ) ^ (-u)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_forall_cpow_mul_eval_eq_of_forall_lt_re.solution
