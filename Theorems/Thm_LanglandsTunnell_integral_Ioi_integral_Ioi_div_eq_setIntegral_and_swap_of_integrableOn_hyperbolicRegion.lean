import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion
    (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
    (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
      (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion.solution
