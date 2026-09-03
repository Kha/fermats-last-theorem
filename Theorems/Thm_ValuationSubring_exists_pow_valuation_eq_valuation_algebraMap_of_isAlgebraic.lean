import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic

theorem ValuationSubring.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic
    {E F : Type*} [Field E] [Field F] [Algebra E F] [Algebra.IsAlgebraic E F]
    (O : ValuationSubring F) {g : F} (hg : g ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : E, c ≠ 0 ∧ O.valuation (g ^ n) = O.valuation (algebraMap E F c) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic.solution
