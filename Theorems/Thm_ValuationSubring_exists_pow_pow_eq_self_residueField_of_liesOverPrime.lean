import Mathlib
import Definitions.Def_ValuationSubring_ReduceAt
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
set_option autoImplicit false

theorem ValuationSubring.exists_pow_pow_eq_self_residueField_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q)
    (a : IsLocalRing.ResidueField A) :
    ∃ r : ℕ, 0 < r ∧ a ^ q ^ r = a := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime.solution
