import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel
    (a : ℝ) (ha : a ≠ 0) (α β : ℝ) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      (1 - η) * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))
        ≤ ∫ w in Icc (Real.exp ((1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y / (Real.pi * |a|))))) / a ^ 2) - δ))
                   (Real.exp ((1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y / (Real.pi * |a|))))) / a ^ 2) + δ)),
          ∫ r in Icc (Real.exp (((1/3 : ℝ) * Real.log (y / (Real.pi * |a|)) -
                        (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y / (Real.pi * |a|))))) / a ^ 2)) - δ))
                     (Real.exp (((1/3 : ℝ) * Real.log (y / (Real.pi * |a|)) -
                        (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y / (Real.pi * |a|))))) / a ^ 2)) + δ)),
          (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel.solution
