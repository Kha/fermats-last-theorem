import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ne_zero_and_v_le_of_liesOverPrime

set_option autoImplicit false

theorem ValuationSubring.exists_ne_zero_and_v_le_of_liesOverPrime
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ε : A.ValueGroup) (hε : ε ≠ 0) :
    ∃ y : A.valuation.Completion, y ≠ 0 ∧ Valued.v y ≤ ε := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ne_zero_and_v_le_of_liesOverPrime.solution
