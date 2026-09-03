import Mathlib
import P2M.Util
import P2M.Sol.S_MellinParseval_setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MellinParseval.setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul
    (a : ℝ → ℂ) (_ha : Integrable a) (_hac : Continuous a)
    (_hap : IntegrableOn (fun y : ℝ => ((y ^ (-(0 : ℝ)) / y : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * a t) (Set.Ioi 0))
    (t₀ : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (-((t₀ : ℂ) * Complex.I)) *
        ∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t) = ((2 * Real.pi : ℝ) : ℂ) * a t₀ := by p2m_exact_reverting @_root_.P2MW.S_MellinParseval_setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul.solution
