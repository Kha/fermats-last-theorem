import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet

set_option autoImplicit false

theorem LanglandsTunnell.casimir_pos_or_discrete_or_zero_of_weightSet
    (lam : ℝ) (S : Set ℤ) (hS : S.Nonempty)
    (hminus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n - 2))
    (hplus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n + 2))
    (clminus : ∀ n ∈ S, 0 < 4 * lam + n * (n - 2) → n - 2 ∈ S)
    (clplus : ∀ n ∈ S, 0 < 4 * lam + n * (n + 2) → n + 2 ∈ S) :
    0 < lam ∨
      (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ∀ n ∈ S, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
      (lam = 0 ∧ (0 : ℤ) ∈ S) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet.solution
