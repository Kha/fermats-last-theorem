import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_prime_pow_eq_one

theorem ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_prime_pow_eq_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q)
    (k : ℕ) (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p ^ k = 1) :
    σ ζ = ζ ^ q := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_prime_pow_eq_one.solution
