import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero

set_option autoImplicit false

open Topology Polynomial

theorem Complex.exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero
    (F : Polynomial (Polynomial ℂ)) (z₀ w₀ : ℂ)
    (h₀ : F.evalEval z₀ w₀ = 0) (hd : (Polynomial.derivative F).evalEval z₀ w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : ℂ → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ F.evalEval z (φ z) = 0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, F.evalEval z w = 0 → w = φ z) := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero.solution
