import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero

theorem Complex.exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero {r : ℕ} {φ : ℂ → Fin r → ℂ} {c : ℂ}
    {R : ℝ} (hR : 0 < R) (hφ : ∀ i, DifferentiableOn ℂ (fun z ↦ φ z i) (Metric.ball c R))
    (hw : ∃ p : Fin r × Fin r,
      φ c p.1 * deriv (fun z ↦ φ z p.2) c - φ c p.2 * deriv (fun z ↦ φ z p.1) c ≠ 0) :
    ∃ ρ > 0, ∃ C > 0, ∀ z ∈ Metric.ball c ρ, ∀ w ∈ Metric.ball c ρ,
      C * ‖z - w‖ ≤ ⨆ p : Fin r × Fin r, ‖φ z p.1 * φ w p.2 - φ z p.2 * φ w p.1‖ := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero.solution
