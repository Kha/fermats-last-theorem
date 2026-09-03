import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime

set_option autoImplicit false

p2m_open "ValuationSubring~valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime"

theorem ValuationSubring.exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ L₁ L₂ : Subfield A.valuation.Completion,
      ratClosure A ≤ L₁ ∧ ratClosure A ≤ L₂ ∧
      IsClosed (L₁ : Set A.valuation.Completion) ∧ IsClosed (L₂ : Set A.valuation.Completion) ∧
      L₁ ⊓ L₂ = ratClosure A ∧
      ¬ ((L₁ : Set A.valuation.Completion) \ ↑(ratClosure A)).Countable ∧
      ¬ ((L₂ : Set A.valuation.Completion) \ ↑(ratClosure A)).Countable := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime.solution
