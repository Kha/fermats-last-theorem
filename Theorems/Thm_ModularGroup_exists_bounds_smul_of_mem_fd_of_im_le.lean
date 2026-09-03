import Mathlib
import P2M.Util
import P2M.Sol.S_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le

open scoped UpperHalfPlane MatrixGroups

theorem ModularGroup.exists_bounds_smul_of_mem_fd_of_im_le (S : Finset SL(2, ℤ)) (Y : ℝ) :
    ∃ B y₀ Y₁ : ℝ, 0 < y₀ ∧ ∀ σ ∈ S, ∀ z ∈ ModularGroup.fd, z.im ≤ Y →
      |(σ • z).re| ≤ B ∧ y₀ ≤ (σ • z).im ∧ (σ • z).im ≤ Y₁ := by p2m_exact_reverting @_root_.P2MW.S_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le.solution
