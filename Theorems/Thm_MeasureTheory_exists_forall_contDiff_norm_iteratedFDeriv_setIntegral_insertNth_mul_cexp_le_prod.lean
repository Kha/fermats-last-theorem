import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod
    {n d : ℕ} (W : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ)) (j : Fin (d + 1)), W (p.1, p.2 + Pi.single j 1) = W p)
    (j : Fin (d + 1)) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m' : Fin d → ℤ,
      let g : (Fin (n + 1) → ℝ) × ℝ → ℂ := fun p =>
        ∫ θ' in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
          W (p.1, Fin.insertNth j p.2 θ') *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m' j' : ℝ) * θ' j' : ℝ) : ℂ)))
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ k, R < |p.1 k|) → g p = 0) ∧
        (∀ p : (Fin (n + 1) → ℝ) × ℝ, g (p.1, p.2 + 1) = g p) ∧
        ∀ i : ℕ, i ≤ N → ∀ p : (Fin (n + 1) → ℝ) × ℝ,
          ‖iteratedFDeriv ℝ i g p‖ ≤ M * ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod.solution
