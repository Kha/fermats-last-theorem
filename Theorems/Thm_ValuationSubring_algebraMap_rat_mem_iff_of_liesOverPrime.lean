import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime

theorem ValuationSubring.algebraMap_rat_mem_iff_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime] (hA : A.LiesOverPrime q) (x : ℚ) :
    algebraMap ℚ (AlgebraicClosure ℚ) x ∈ A ↔ x ∈ (Rat.padicValuation q).valuationSubring := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime.solution
