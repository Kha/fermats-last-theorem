import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import P2M.Util
import P2M.Sol.S_Complex_forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re

set_option autoImplicit false

theorem Complex.forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re
    (N : ℝ) (hN : 0 < N) (σ₂ σ₀ : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {s : ℂ | σ₂ < s.re})
    (P Q : Polynomial ℂ)
    (h : ∀ s : ℂ, σ₀ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = P.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, σ₂ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = P.eval ((N : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_Complex_forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re.solution
