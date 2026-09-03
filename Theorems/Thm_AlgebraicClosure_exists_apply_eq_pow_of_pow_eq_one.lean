import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one

theorem AlgebraicClosure.exists_apply_eq_pow_of_pow_eq_one (n : ℕ) (hn : n ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one.solution
