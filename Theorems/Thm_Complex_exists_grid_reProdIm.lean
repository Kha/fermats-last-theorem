import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_grid_reProdIm

theorem Complex.exists_grid_reProdIm {a₁ a₂ b₁ b₂ δ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hδ : 0 < δ) :
    ∃ (m n : ℕ) (c : Fin (m + 1) × Fin (n + 1) → ℂ),
      (∀ i, c i ∈ Set.Icc a₁ a₂ ×ℂ Set.Icc b₁ b₂) ∧
      (∀ w ∈ Set.Icc a₁ a₂ ×ℂ Set.Icc b₁ b₂, ∃ i, dist w (c i) < δ) ∧
      (∀ i j, ∃ (L : ℕ) (π : ℕ → Fin (m + 1) × Fin (n + 1)),
        L ≤ m + n ∧ π 0 = i ∧ π L = j ∧ ∀ l < L, dist (c (π l)) (c (π (l + 1))) ≤ δ) := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_grid_reProdIm.solution
