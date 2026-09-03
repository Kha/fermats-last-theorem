import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic

theorem ValuationSubring.exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {p : ℕ} (hp : p.Prime) (hAp : A.valuation (p : K) < 1)
    {x : K} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ, A.valuation x ^ n = A.valuation (p : K) ^ k := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic.solution
