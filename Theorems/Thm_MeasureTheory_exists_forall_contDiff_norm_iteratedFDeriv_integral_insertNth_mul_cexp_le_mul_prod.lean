import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod
    (n N : ℕ) (k : Fin (n + 1)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : (Fin (n + 1) → ℝ) × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ i, R < |p.1 i|) → g p = 0) →
      ∀ M : ℝ, (∀ i : ℕ, i ≤ N + 2 * n → ∀ p : (Fin (n + 1) → ℝ) × ℝ, ‖iteratedFDeriv ℝ i g p‖ ≤ M) →
      ∀ ξ' : Fin n → ℝ,
        let h : ℝ × ℝ → ℂ := fun q =>
          ∫ x' : Fin n → ℝ, g (Fin.insertNth k q.1 x', q.2) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ)))
        ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ q : ℝ × ℝ, R < |q.1| → h q = 0) ∧
          ∀ i : ℕ, i ≤ N → ∀ q : ℝ × ℝ,
            ‖iteratedFDeriv ℝ i h q‖ ≤ K * M * ∏ i', (1 + |ξ' i'|)⁻¹ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod.solution
