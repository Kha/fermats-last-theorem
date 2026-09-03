import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_intCast_lt_one_of_dvd

theorem ValuationSubring.valuation_intCast_lt_one_of_dvd {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hA : A.valuation (q : K) < 1) {a : ℤ} (hqa : (q : ℤ) ∣ a) :
    A.valuation (a : K) < 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_intCast_lt_one_of_dvd.solution
