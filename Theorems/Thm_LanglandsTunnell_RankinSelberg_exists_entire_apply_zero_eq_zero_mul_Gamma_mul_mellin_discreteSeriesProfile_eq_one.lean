import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_discreteSeriesProfile_eq_one

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.RankinSelberg.exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_discreteSeriesProfile_eq_one
    (C k : ℝ) (hC : 0 < C) (hk : 0 < k) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ H 0 = 0 ∧
      ∀ s : ℂ, 1 - k < s.re → 0 < s.re →
        H s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, (((if 0 < y then C * y ^ k * Real.exp (-(4 * Real.pi * y)) else 0 : ℝ) : ℝ) : ℂ) *
            ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_discreteSeriesProfile_eq_one.solution
