import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import P2M.Util
import P2M.Sol.S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ z : ℂ, ((‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4 : ℝ) : ℂ) * G ((b + z * d) / (a + z * c))
      = ∫ u : ℂ, G u := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex.solution
