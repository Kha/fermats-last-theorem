import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime

theorem ValuationSubring.exists_integral_mul_eq_of_liesOverPrime (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) : ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧ a * s = x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.solution
