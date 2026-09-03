import Mathlib
import P2M.Util
import P2M.Sol.S_MellinParseval_integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two

set_option autoImplicit false

open MeasureTheory

theorem MellinParseval.integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two
    (σ : ℝ) (a : ℝ → ℂ) (_ha : Integrable a) (_ha2 : MemLp a 2) :
    IntegrableOn (fun y : ℝ => (y ^ (-(2 * σ)) / y) *
        ‖∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) * a t‖ ^ 2) (Set.Ioi 0) ∧
    ∫ y in Set.Ioi (0 : ℝ), (y ^ (-(2 * σ)) / y) *
        ‖∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) * a t‖ ^ 2
      = 2 * Real.pi * ∫ t : ℝ, ‖a t‖ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MellinParseval_integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two.solution
