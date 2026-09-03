import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat

theorem ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
    {p : ℕ} (hp : p.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat.solution
