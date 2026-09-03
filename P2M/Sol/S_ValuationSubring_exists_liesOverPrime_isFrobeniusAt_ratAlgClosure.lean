import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure

open scoped MatrixGroups

theorem solution (p : Nat.Primes) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime (p : ℕ) ∧ A.IsFrobeniusAt σ (p : ℕ) := by
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat p
  obtain ⟨σ, hσ⟩ :=
    ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat p.2 hA
  exact ⟨A, σ, hA, hσ⟩
