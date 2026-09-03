import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure

open scoped MatrixGroups
theorem ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
    (p : Nat.Primes) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime (p : ℕ) ∧ A.IsFrobeniusAt σ (p : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure.solution
