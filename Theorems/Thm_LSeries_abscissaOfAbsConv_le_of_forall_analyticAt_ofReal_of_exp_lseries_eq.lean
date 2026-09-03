import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import P2M.Util
import P2M.Sol.S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq

set_option autoImplicit false

open scoped ComplexOrder

theorem LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
    (d : ℕ → ℝ) (hd : ∀ n : ℕ, 0 ≤ d n) (Λ : ℂ → ℂ) (x σ₀ : ℝ)
    (han : ∀ σ : ℝ, x < σ → AnalyticAt ℂ Λ (σ : ℂ))
    (heq : ∀ s : ℂ, σ₀ < s.re →
      LSeriesSummable (fun n => (d n : ℂ)) s ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) s) = Λ s) :
    LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ (x : EReal) ∧
      ∀ σ : ℝ, x < σ →
        LSeriesSummable (fun n => (d n : ℂ)) σ ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) σ) = Λ σ := by p2m_exact_reverting @_root_.P2MW.S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq.solution
