import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair

theorem Module.exists_basis_padicValRat_apply_nonneg_iff_pair
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M] (p : ℕ) [Fact p.Prime]
    (a a' : ℤ → M →ₗ[ℚ] ℚ) (hinj' : ∀ x, (∀ m, a' m x = 0) → x = 0)
    (hbd : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a m x))
    (hbd' : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a' m x))
    (hsub : ∀ x, (∀ m, 0 ≤ padicValRat p (a m x)) → ∀ m, 0 ≤ padicValRat p (a' m x))
    (u : M) (hu : ∀ m, 0 ≤ padicValRat p (a m u))
    (hprim : ∃ m, a' m u ≠ 0 ∧ padicValRat p (a' m u) = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ M) (e : Fin n → ℕ) (i₀ : Fin n), b i₀ = u ∧ e i₀ = 0 ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a m (∑ i, c i • b i))) ↔ ∀ i, 0 ≤ padicValRat p (c i)) ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a' m (∑ i, c i • b i))) ↔
        ∀ i, -(e i : ℤ) ≤ padicValRat p (c i)) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair.solution
