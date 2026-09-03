import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isFrobeniusAt_rat

theorem ValuationSubring.exists_isFrobeniusAt_rat (ℓ : ℕ) (hℓ : ℓ.Prime) : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ ∧ ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isFrobeniusAt_rat.solution
