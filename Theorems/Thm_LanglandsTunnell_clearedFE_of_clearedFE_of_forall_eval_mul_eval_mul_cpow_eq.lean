import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.Polynomial.Eval.Defs
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq

set_option autoImplicit false

theorem LanglandsTunnell.clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq
    (N : ℕ) (hN : 1 < N)
    (RA₁ RA₂ RB₁ RB₂ : Polynomial ℂ) (rA rB : ℤ) (hRA₂ : RA₂ ≠ 0)
    (hΓ : ∀ s : ℂ, RB₂.eval ((N : ℂ) ^ s) * (RA₁.eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rA : ℂ) * s)) =
      RA₂.eval ((N : ℂ) ^ s) * (RB₁.eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rB : ℂ) * s)))
    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ)
    (hA : ∀ s : ℂ, (RA₂).eval ((N : ℂ) ^ s) * (((N : ℂ) ^ ((md : ℂ) * s)) * Pd.eval ((N : ℂ) ^ (-s))) * Q.eval ((N : ℂ) ^ s) =
          ((RA₁).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rA : ℂ) * s)) * (((N : ℂ) ^ ((m : ℂ) * (-s))) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (RB₂).eval ((N : ℂ) ^ s) * (((N : ℂ) ^ ((md : ℂ) * s)) * Pd.eval ((N : ℂ) ^ (-s))) * Q.eval ((N : ℂ) ^ s) =
          ((RB₁).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rB : ℂ) * s)) * (((N : ℂ) ^ ((m : ℂ) * (-s))) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq.solution
