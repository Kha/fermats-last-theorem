import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat

set_option autoImplicit false

theorem ValuationSubring.exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat
    (P : ValuationSubring (AlgebraicClosure ℚ)) :
    ∀ x : AlgebraicClosure ℚ, x ≠ 0 → ∀ y : P, y ∈ IsLocalRing.maximalIdeal P →
      ∃ n : ℕ, P.valuation ((y : AlgebraicClosure ℚ) ^ n) ≤ P.valuation x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat.solution
