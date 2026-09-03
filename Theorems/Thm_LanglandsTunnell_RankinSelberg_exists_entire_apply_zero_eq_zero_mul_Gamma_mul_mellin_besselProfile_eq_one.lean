import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one

set_option autoImplicit false

p2m_open "MeasureTheory LanglandsTunnell.ArchBessel~mellin_besselKernel_mul_besselKernel_eq"

theorem LanglandsTunnell.RankinSelberg.exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one
    (C : ℝ) (hC : 0 < C) (a : ℕ) (ha : 1 ≤ a) (ν : ℂ) (hν : a = 1 → ν.re = 0 ∨ ν.im = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ H 0 = 0 ∧
      ∀ s : ℂ, 1 - (a : ℝ) + 2 * |ν.re| < s.re → 0 < s.re →
        H s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, (((C * |y| ^ a * ‖besselKernel ν (2 * Real.pi * |y|)‖ ^ 2 : ℝ) : ℝ) : ℂ) *
            ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one.solution
