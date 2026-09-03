import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg

set_option autoImplicit false

theorem Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
    (F₁ F₂ : ℂ → ℂ) (β γ r 𝓛 C₀ : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (h𝓛 : 1 ≤ r * 𝓛) (hC₀ : 0 ≤ C₀) (hC₀𝓛 : C₀ ≤ 𝓛)
    (hρ : F₁ ((β : ℂ) + γ * Complex.I) = 0)
    (h1nz : ∀ s : ℂ, 1 < s.re → F₁ s ≠ 0)
    (h2nz : ∀ s : ℂ, 1 < s.re → F₂ s ≠ 0)
    (h1an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₁ (Metric.closedBall ((σ : ℂ) + γ * Complex.I) r))
    (h2an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₂ (Metric.closedBall ((σ : ℂ) + 2 * γ * Complex.I) r))
    (h1up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + γ * Complex.I) r, ‖F₁ s‖ ≤ Real.exp 𝓛)
    (h2up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + 2 * γ * Complex.I) r, ‖F₂ s‖ ≤ Real.exp 𝓛)
    (h1lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₁ ((σ : ℂ) + γ * Complex.I)‖)
    (h2lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₂ ((σ : ℂ) + 2 * γ * Complex.I)‖)
    (h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      0 ≤ 3 * (1 / (σ - 1) + C₀)
        + 4 * (-(deriv F₁ ((σ : ℂ) + γ * Complex.I) / F₁ ((σ : ℂ) + γ * Complex.I))).re
        + (-(deriv F₂ ((σ : ℂ) + 2 * γ * Complex.I) / F₂ ((σ : ℂ) + 2 * γ * Complex.I))).re) :
    r / (20000 * 𝓛) ≤ 1 - β := by p2m_exact_reverting @_root_.P2MW.S_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg.solution
