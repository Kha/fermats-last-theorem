import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg

set_option autoImplicit false

theorem AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
    (a b : ℕ) (t : ℂ) (ht : ((a : ℝ) + b) / 2 + 1 < t.re) :
    ∫ z : ℂ, z ^ a * (starRingEnd ℂ z) ^ b * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)
      = if a = b then (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t
        else 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg.solution
