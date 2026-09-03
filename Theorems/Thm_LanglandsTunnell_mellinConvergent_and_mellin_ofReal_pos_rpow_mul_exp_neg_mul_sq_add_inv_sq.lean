import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Exponential
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq (b : ℝ) (hb : 0 < b) (N : ℝ) :
    (∀ s : ℂ, MellinConvergent (fun w : ℝ => ((w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) : ℝ) : ℂ)) s) ∧
    ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧
      mellin (fun w : ℝ => ((w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) : ℝ) : ℂ)) (x : ℂ) = (r : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq.solution
