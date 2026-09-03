import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg

set_option autoImplicit false

open MeasureTheory Set

theorem Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
    (α β γ : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < (α + β - γ).re) :
    Integrable (fun p : ℝ × ℝ => Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
        (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
      ∫ p : ℝ × ℝ, Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
          (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ)
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) =
        Complex.Gamma (α + β - γ) * Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β) := by p2m_exact_reverting @_root_.P2MW.S_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg.solution
