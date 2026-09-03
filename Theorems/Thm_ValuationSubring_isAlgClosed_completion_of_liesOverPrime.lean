import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isAlgClosed_completion_of_liesOverPrime

theorem ValuationSubring.isAlgClosed_completion_of_liesOverPrime
    (p : ℕ) (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    IsAlgClosed A.valuation.Completion := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isAlgClosed_completion_of_liesOverPrime.solution
