import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg

theorem ValuationSubring.ratCast_mem_iff_padicValRat_nonneg {K : Type*} [Field K] [CharZero K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : (r : K) ∈ A ↔ 0 ≤ padicValRat q r := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg.solution
