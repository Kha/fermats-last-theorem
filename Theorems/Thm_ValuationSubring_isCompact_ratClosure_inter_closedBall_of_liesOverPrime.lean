import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime

set_option autoImplicit false

open ValuationSubring

theorem ValuationSubring.isCompact_ratClosure_inter_closedBall_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∀ ρ : A.ValueGroup, IsCompact {x : A.valuation.Completion |
      x ∈ Set.range (algebraMap (↥(ratClosure A)) A.valuation.Completion) ∧ Valued.v x ≤ ρ} := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime.solution
