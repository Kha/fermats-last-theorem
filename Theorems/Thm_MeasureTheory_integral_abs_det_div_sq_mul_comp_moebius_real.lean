import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import P2M.Util
import P2M.Sol.S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (G : ℝ → ℂ) :
    ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
      = ∫ u : ℝ, G u := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real.solution
