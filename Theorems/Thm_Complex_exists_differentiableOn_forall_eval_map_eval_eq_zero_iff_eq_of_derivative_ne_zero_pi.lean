import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi

set_option autoImplicit false

open Topology Polynomial

theorem Complex.exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi
    {n : ℕ} (F : Polynomial (MvPolynomial (Fin n) ℂ)) (z₀ : Fin n → ℂ) (w₀ : ℂ)
    (h₀ : (F.map (MvPolynomial.eval z₀)).eval w₀ = 0)
    (hd : ((Polynomial.derivative F).map (MvPolynomial.eval z₀)).eval w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : (Fin n → ℂ) → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧ ContDiffOn ℂ ⊤ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ (F.map (MvPolynomial.eval z)).eval (φ z) = 0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, (F.map (MvPolynomial.eval z)).eval w = 0 → w = φ z) := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi.solution
