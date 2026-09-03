import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime

set_option autoImplicit false

p2m_open "ValuationSubring~mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one"

theorem ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    0 < Valued.v (algebraMap (↥(ratClosure A)) A.valuation.Completion ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩) ∧
    Valued.v (algebraMap (↥(ratClosure A)) A.valuation.Completion ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩) < 1 ∧
    (∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime.solution
