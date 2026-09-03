import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_isRoot_and_valuation_lt_one

open Polynomial
theorem Polynomial.exists_isRoot_and_valuation_lt_one {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K) {f : Polynomial K} (h0 : A.valuation (f.coeff 0) < 1) {n : ℕ} (hn : A.valuation (f.coeff n) = 1) : ∃ r : K, f.IsRoot r ∧ A.valuation r < 1 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_isRoot_and_valuation_lt_one.solution
