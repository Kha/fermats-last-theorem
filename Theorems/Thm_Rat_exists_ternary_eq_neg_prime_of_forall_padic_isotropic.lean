import Mathlib
import P2M.Util
import P2M.Sol.S_Rat_exists_ternary_eq_neg_prime_of_forall_padic_isotropic

theorem Rat.exists_ternary_eq_neg_prime_of_forall_padic_isotropic (p : ℕ) [Fact p.Prime] (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0) (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∃ z x y : ℚ_[ℓ], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - (u : ℚ_[ℓ]) * x ^ 2 - (v : ℚ_[ℓ]) * y ^ 2 = 0) : ∃ x y z : ℚ, u * x ^ 2 + v * y ^ 2 - u * v * z ^ 2 = -p := by p2m_exact_reverting @_root_.P2MW.S_Rat_exists_ternary_eq_neg_prime_of_forall_padic_isotropic.solution
