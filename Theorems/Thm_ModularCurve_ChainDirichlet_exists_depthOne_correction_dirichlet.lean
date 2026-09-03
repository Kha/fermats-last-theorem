import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet

theorem ModularCurve.ChainDirichlet.exists_depthOne_correction_dirichlet {ι : Type*} [Finite ι] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i)
    (r : ι → ℕ → ℤ) :
    ∃ (ν : ι → ℤ) (c : ι → ℕ → ℤ),
      (∀ i, n i = 1 → ν i = 0) ∧ (∀ i, c i 0 = 0) ∧ (∀ i d, n i ≤ d → c i d = 0) ∧
      ∀ i d, 1 ≤ d → d + 1 ≤ n i →
        c i (d - 1) - 2 * c i d + c i (d + 1) = -(if d = 1 then r i d - ν i else r i d) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet.solution
