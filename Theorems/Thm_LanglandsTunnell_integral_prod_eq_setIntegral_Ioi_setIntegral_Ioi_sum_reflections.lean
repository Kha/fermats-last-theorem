import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
    (F : ℝ × ℝ → ℂ) (hF : Integrable F ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ p : ℝ × ℝ, F p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), (F (t, y) + F (-t, y) + F (t, -y) + F (-t, -y)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections.solution
