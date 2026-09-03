import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_intCast_eq_pow_padicValInt

theorem ValuationSubring.valuation_intCast_eq_pow_padicValInt {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {z : ℤ} (hz : z ≠ 0) : A.valuation (z : K) = A.valuation (q : K) ^ padicValInt q z := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_intCast_eq_pow_padicValInt.solution
