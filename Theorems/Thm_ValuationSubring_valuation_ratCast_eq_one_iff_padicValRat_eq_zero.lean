import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_ratCast_eq_one_iff_padicValRat_eq_zero

theorem ValuationSubring.valuation_ratCast_eq_one_iff_padicValRat_eq_zero {K : Type*} [Field K]
    [CharZero K] (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : A.valuation (r : K) = 1 ↔ padicValRat q r = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_ratCast_eq_one_iff_padicValRat_eq_zero.solution
