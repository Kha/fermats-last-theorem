import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi
    (F : ℝ × ℝ × ℝ → ℂ) (hFm : Measurable F)
    (hF : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod
      ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))) :
    Integrable (fun p : ℝ × ℝ × ℝ =>
        ((p.2.1 / (p.1 * p.2.2 ^ 2) : ℝ) : ℂ) * F (p.1, -(p.2.1 / p.1), p.2.1 / p.2.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi.solution
