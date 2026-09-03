import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat

theorem ValuationSubring.valuation_ratCast_eq_zpow_padicValRat {K : Type*} [Field K] [CharZero K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : A.valuation (r : K) = A.valuation (q : K) ^ padicValRat q r := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat.solution
