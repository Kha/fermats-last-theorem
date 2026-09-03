import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod
    {n d : ℕ} (W : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ)) (j : Fin (d + 1)), W (p.1, p.2 + Pi.single j 1) = W p)
    (k : Fin (n + 1)) (j : Fin (d + 1)) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ξ' : Fin n → ℝ) (m' : Fin d → ℤ),
      let h : ℝ × ℝ → ℂ := fun q =>
        ∫ x' : Fin n → ℝ, ∫ θ' in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
          W (Fin.insertNth k q.1 x', Fin.insertNth j q.2 θ') *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m' j' : ℝ) * θ' j' : ℝ) : ℂ)))
      ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ q : ℝ × ℝ, R < |q.1| → h q = 0) ∧ (∀ q : ℝ × ℝ, h (q.1, q.2 + 1) = h q) ∧
        ∀ i : ℕ, i ≤ N → ∀ q : ℝ × ℝ,
          ‖iteratedFDeriv ℝ i h q‖ ≤ M * (∏ i', (1 + |ξ' i'|)⁻¹ ^ 2) * ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_setIntegral_insertNth_mul_cexp_le_prod.solution
