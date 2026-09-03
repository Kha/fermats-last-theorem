import Mathlib
import P2M.Util
import P2M.Sol.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime_nsmul

theorem SubtractionMonoid.exists_zsmul_eq_of_forall_prime_nsmul {A : Type*}
    [SubtractionMonoid A] (h : ∀ p : ℕ, p.Prime → ∀ x : A, ∃ y : A, p • y = x) :
    ∀ n : ℤ, n ≠ 0 → ∀ x : A, ∃ y : A, n • y = x := by p2m_exact_reverting @_root_.P2MW.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime_nsmul.solution
