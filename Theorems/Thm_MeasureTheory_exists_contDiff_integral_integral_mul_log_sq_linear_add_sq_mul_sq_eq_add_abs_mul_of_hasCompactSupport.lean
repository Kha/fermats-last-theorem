import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℝ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (c₀ : P → ℝ) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀) (hc₀0 : ∀ p, c₀ p ≠ 0)
    (φ : P → (V →L[ℝ] ℝ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (θ : P × V → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ0 : ∀ q, 0 ≤ θ q) :
    ∃ A B : P × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (ρ : ℝ),
        Integrable (fun sv : ℝ × V =>
          g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ)) ((volume : Measure ℝ).prod μ) ∧
        ∫ sv : ℝ × V, g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ) ∂((volume : Measure ℝ).prod μ) =
          A (p, ρ) + ((|ρ| : ℝ) : ℂ) * B (p, ρ) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport.solution
