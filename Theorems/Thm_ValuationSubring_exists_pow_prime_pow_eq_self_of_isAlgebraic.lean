import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_pow_prime_pow_eq_self_of_isAlgebraic

theorem ValuationSubring.exists_pow_prime_pow_eq_self_of_isAlgebraic {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℤ K] (A : ValuationSubring K) (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] (x : IsLocalRing.ResidueField A) : ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_pow_prime_pow_eq_self_of_isAlgebraic.solution
