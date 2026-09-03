import Mathlib
import P2M.Util
import P2M.Sol.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime

theorem SubtractionMonoid.exists_zsmul_eq_of_forall_prime {A : Type*} [SubtractionMonoid A]
    (h : ∀ p : ℕ, p.Prime → ∀ x : A, ∃ y : A, (p : ℤ) • y = x) :
    ∀ n : ℤ, n ≠ 0 → ∀ x : A, ∃ y : A, n • y = x := by p2m_exact_reverting @_root_.P2MW.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime.solution
