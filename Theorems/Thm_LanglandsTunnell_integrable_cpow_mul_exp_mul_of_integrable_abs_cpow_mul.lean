import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul
    (w : ℂ) (hw : -1 < w.re) (K : ℝ → ℝ → ℝ → ℂ)
    (hK : Measurable fun p : ℝ × ℝ × ℝ => K p.1 p.2.1 p.2.2)
    (h3 : Integrable (fun q : ℝ × ℝ × ℝ => ((|q.2.1| : ℝ) : ℂ) ^ (w + 1) * K q.1 q.2.1 q.2.2)
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))))) :
    Integrable (fun p : ℝ × ℝ × ℝ × ℝ =>
        ((p.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (p.1 ^ 2 * (p.2.2.1 ^ 2)⁻¹))) : ℂ) * K p.2.1 p.2.2.1 p.2.2.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul.solution
