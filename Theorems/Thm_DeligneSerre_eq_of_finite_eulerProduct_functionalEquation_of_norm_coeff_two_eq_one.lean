import Mathlib
import P2M.Util
import P2M.Sol.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one

set_option autoImplicit false

open Polynomial

theorem DeligneSerre.eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℤ) (ω : ℂ) (hω : ω ≠ 0)
    (P Q P' Q' : ℕ → ℂ[X])
    (hP₀ : ∀ p ∈ S, (P p).coeff 0 = 1) (hQ₀ : ∀ p ∈ S, (Q p).coeff 0 = 1)
    (hP'₀ : ∀ p ∈ S, (P' p).coeff 0 = 1) (hQ'₀ : ∀ p ∈ S, (Q' p).coeff 0 = 1)
    (hP : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → 1 < ‖z‖ ^ 2 * p)
    (hP' : ∀ p ∈ S, ∀ z : ℂ, (P' p).IsRoot z → 1 < ‖z‖ ^ 2 * p)
    (hQ : ∀ p ∈ S,
      ((∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∧
          ∀ z : ℂ, (Q' p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1) ∧ (∀ z : ℂ, (P' p).IsRoot z → ‖z‖ = 1) ∧
          (Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1 ∧
          (Q' p).natDegree ≤ 2 ∧ ‖(Q' p).coeff 2‖ = 1))
    (σ₀ : ℝ)
    (hFE : ∀ s : ℝ, σ₀ ≤ s →
      (∏ p ∈ S, ((p : ℂ) ^ (-(s : ℂ))) ^ (e p)) *
          ∏ p ∈ S, (P' p).eval ((p : ℂ) ^ ((s : ℂ) - 1)) * (Q p).eval ((p : ℂ) ^ (-(s : ℂ))) =
        ω * ∏ p ∈ S, (P p).eval ((p : ℂ) ^ (-(s : ℂ))) * (Q' p).eval ((p : ℂ) ^ ((s : ℂ) - 1))) :
    ∀ p ∈ S, e p = 0 ∧ P p = Q p ∧ P' p = Q' p := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one.solution
