import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_forall_exists_pow_prime_pow_eq_self_residueField

set_option autoImplicit false

theorem ValuationSubring.forall_exists_pow_prime_pow_eq_self_residueField
    {L : Type*} [Field L] [CharZero L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (A : ValuationSubring L)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField ↥A) p] :
    ∀ x : IsLocalRing.ResidueField ↥A, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_forall_exists_pow_prime_pow_eq_self_residueField.solution
