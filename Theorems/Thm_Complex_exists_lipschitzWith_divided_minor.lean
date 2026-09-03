import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_lipschitzWith_divided_minor

open Metric
theorem Complex.exists_lipschitzWith_divided_minor {r : ℕ} {φ : ℂ → Fin r → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hφ : ∀ i, DifferentiableOn ℂ (fun z ↦ φ z i) (Metric.ball c R)) :
    ∃ ρ > 0, ∃ L ≥ 0, ∃ Ψ : ℂ → ℂ → (Fin r × Fin r → ℂ),
      (∀ w ∈ Metric.ball c ρ, ∀ z ∈ Metric.ball c ρ, ∀ p : Fin r × Fin r,
          φ w p.1 * φ z p.2 - φ w p.2 * φ z p.1 = (z - w) * Ψ w z p) ∧
      (∀ w ∈ Metric.ball c ρ, ∀ p : Fin r × Fin r,
          Ψ w w p = φ w p.1 * deriv (fun z ↦ φ z p.2) w - φ w p.2 * deriv (fun z ↦ φ z p.1) w) ∧
      (∀ w ∈ Metric.ball c ρ, ∀ z ∈ Metric.ball c ρ, ∀ z' ∈ Metric.ball c ρ,
          ‖Ψ w z - Ψ w z'‖ ≤ L * ‖z - z'‖) := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_lipschitzWith_divided_minor.solution
