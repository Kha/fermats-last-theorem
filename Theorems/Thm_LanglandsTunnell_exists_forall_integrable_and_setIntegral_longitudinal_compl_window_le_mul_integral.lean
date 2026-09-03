import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral

set_option autoImplicit false

p2m_open "MeasureTheory~setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap Set"

theorem LanglandsTunnell.exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral
    (a : ℝ) (ha : a ≠ 0) (α β : ℝ) (η δ₁ : ℝ) (hη : 0 < η) (hδ₁ : 0 < δ₁) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      Integrable (fun u : ℝ =>
        Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
            + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
          * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ))) ∧
      ∫ u in {u : ℝ | δ₁ < |u - (1 / 3) * Real.log (y / (Real.pi * |a|))|},
          Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
              + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
            * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ))
        ≤ η * ∫ u : ℝ,
          Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
              + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
            * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral.solution
