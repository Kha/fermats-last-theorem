import Mathlib
import P2M.Util
import P2M.Sol.S_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add

set_option autoImplicit false

open MeasureTheory

theorem contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add
    {n : ℕ} (Φ : ℝ × (Fin n → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : ℕ) (x : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) ∧
    ∀ (N : ℕ) (y : Fin n → ℝ),
      ‖iteratedFDeriv ℝ N (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) y‖ ≤
        ‖iteratedFDeriv ℝ (N + j) Φ (x, y)‖ := by p2m_exact_reverting @_root_.P2MW.S_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add.solution
