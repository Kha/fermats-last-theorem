import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime

open scoped Pointwise
theorem ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime {q : ℕ} (hq : q.Prime) (A A₀ : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (hA₀ : A₀.LiesOverPrime q) : ∃ g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), g • A = A₀ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime.solution
