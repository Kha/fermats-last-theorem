import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
    (a : ℝ) (ha : a ≠ 0) (A B : ℂ) (τ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      (1 - ε) * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          ‖((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((y : ℂ) + (τ : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)‖
        ≤ ‖∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          ((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((y : ℂ) + (τ : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)‖ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral.solution
