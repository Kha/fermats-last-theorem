import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_circleIntegral_div_sub_eq_sum_div_deriv

theorem Complex.circleIntegral_div_sub_eq_sum_div_deriv {R Ψ : ℂ → ℂ} {c t : ℂ} {r : ℝ}
    (hr : 0 < r) (hR : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ R z)
    (hΨ : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ Ψ z)
    (hne : ∀ z ∈ Metric.sphere c r, R z ≠ t) (Z : Finset ℂ)
    (hZ : ∀ a, a ∈ Z ↔ a ∈ Metric.ball c r ∧ R a = t) (hsimple : ∀ a ∈ Z, deriv R a ≠ 0) :
    (∮ z in C(c, r), Ψ z / (R z - t)) =
      2 * Real.pi * Complex.I * ∑ a ∈ Z, Ψ a / deriv R a := by p2m_exact_reverting @_root_.P2MW.S_Complex_circleIntegral_div_sub_eq_sum_div_deriv.solution
