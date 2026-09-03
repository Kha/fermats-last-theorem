import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_pow_valuation_ratClosure_natCast_le_of_liesOverPrime

set_option autoImplicit false

p2m_open "ValuationSubring~valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime"

theorem ValuationSubring.exists_pow_valuation_ratClosure_natCast_le_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∀ ε : A.ValueGroup, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap (↥(ratClosure A)) A.valuation.Completion ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩) ^ N ≤ ε := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_pow_valuation_ratClosure_natCast_le_of_liesOverPrime.solution
