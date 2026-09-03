import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic

set_option autoImplicit false

theorem ValuationSubring.exists_valuation_pow_lt_of_isAlgebraic
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] (O : ValuationSubring F)
    {π₀ : F} (h0 : O.valuation π₀ ≠ 0) (h1 : O.valuation π₀ < 1) (γ : O.ValueGroup) (hγ : γ ≠ 0) :
    ∃ n : ℕ, O.valuation π₀ ^ n < γ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic.solution
