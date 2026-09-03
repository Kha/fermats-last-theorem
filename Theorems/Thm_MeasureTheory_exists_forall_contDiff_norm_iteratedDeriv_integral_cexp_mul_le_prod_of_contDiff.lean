import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × (Fin n → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) h →
        (∀ p : ℝ × (Fin n → ℝ), R < |p.1| → h p = 0) → (∀ p : ℝ × (Fin n → ℝ), (∃ k, R < |p.2 k|) → h p = 0) →
      ∀ M : ℝ, (∀ N : ℕ, N ≤ 2 * n + 2 → ∀ p : ℝ × (Fin n → ℝ), ‖iteratedFDeriv ℝ N h p‖ ≤ M) →
      ∀ ξ : Fin n → ℝ,
        ContDiff ℝ 2 (fun x : ℝ =>
          ∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) ∧
        (∀ x : ℝ, R < |x| →
          (∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) = 0) ∧
        ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
          ‖iteratedDeriv j (fun x : ℝ =>
              ∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) x‖ ≤
            K * M * ∏ k, (1 + |ξ k|)⁻¹ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff.solution
