import Mathlib
import P2M.Util
import P2M.Sol.S_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff

set_option autoImplicit false

theorem Real.abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff :
    (∀ X : ℝ, |1 - (Real.exp X)⁻¹| = Real.exp (-X) * |1 - Real.exp X|) ∧
    (∀ X : ℝ, |1 - (-Real.exp X)⁻¹| = 1 + Real.exp (-X)) ∧
    (∀ X : ℝ, 0 < 1 + Real.exp (-X)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun X : ℝ => 1 + Real.exp (-X)) := by p2m_exact_reverting @_root_.P2MW.S_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff.solution
