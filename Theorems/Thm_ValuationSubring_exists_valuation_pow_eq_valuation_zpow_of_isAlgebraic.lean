import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic

set_option autoImplicit false

theorem ValuationSubring.exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] (O : ValuationSubring F)
    {π₀ : F} (h0 : O.valuation π₀ ≠ 0) (h1 : O.valuation π₀ < 1) {x : F} (hx : x ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ k : ℤ, O.valuation x ^ m = O.valuation π₀ ^ k := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic.solution
