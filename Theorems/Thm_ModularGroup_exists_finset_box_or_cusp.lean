import Mathlib
import P2M.Util
import P2M.Sol.S_ModularGroup_exists_finset_box_or_cusp

open scoped UpperHalfPlane MatrixGroups

theorem ModularGroup.exists_finset_box_or_cusp (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (Y : ℝ) :
    ∃ (S : Finset SL(2, ℤ)) (B y₀ Y₁ : ℝ), 0 < y₀ ∧ ∀ τ : ℍ, ∃ γ ∈ Γ,
      (|(γ • τ).re| ≤ B ∧ y₀ ≤ (γ • τ).im ∧ (γ • τ).im ≤ Y₁) ∨
      (∃ σ ∈ S, ∃ z ∈ ModularGroup.fd, Y < z.im ∧ γ • τ = σ • z) := by p2m_exact_reverting @_root_.P2MW.S_ModularGroup_exists_finset_box_or_cusp.solution
