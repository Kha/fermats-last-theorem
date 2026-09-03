import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

theorem ValuationSubring.exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime]
    (ϖ : AlgebraicClosure ℚ) (eK : ℕ) (heK : 1 ≤ eK) (ε : AlgebraicClosure ℚ) (hε : A.valuation ε = 1)
    (hqϖ : ((q : ℕ) : AlgebraicClosure ℚ) = ϖ ^ eK * ε)
    (E : ℕ) (hE : 1 ≤ E) (a b : AlgebraicClosure ℚ)
    (ha : A.valuation a < 1) (hb : A.valuation b < 1)
    (hab : A.valuation a * A.valuation b = A.valuation ϖ ^ E) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ p : ℕ, 1 ≤ p ∧ p + 1 ≤ r * E ∧ A.valuation a ^ r = A.valuation ϖ ^ p := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one.solution
