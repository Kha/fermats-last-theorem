import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_ratClosure_eq_natCast_of_liesOverPrime

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~exists_pseudoUniformizer_isExhausted_of_isCompact ValuationSubring~isCompact_ratClosure_inter_closedBall_of_liesOverPrime~valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime"

theorem CerednikDrinfeld.Omega.exists_pseudoUniformizer_ratClosure_eq_natCast_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ ϖ : PseudoUniformizer ↥(ValuationSubring.ratClosure A) A.valuation.Completion,
      algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion ϖ.ϖ = ((r : AlgebraicClosure ℚ) : A.valuation.Completion) ∧
      IsExhausted ϖ ∧
      ∀ n : ℕ, ∃ T : Finset ↥(ValuationSubring.ratClosure A), ∀ a : ↥(ValuationSubring.ratClosure A),
        Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion a) ≤ (Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion ϖ.ϖ))⁻¹ ^ n →
          ∃ t ∈ T, Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion a - algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion t) <
            (Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion ϖ.ϖ)) ^ n := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_ratClosure_eq_natCast_of_liesOverPrime.solution
