import Mathlib
import P2M.Util
import P2M.Sol.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le

set_option autoImplicit false

theorem fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le
    {R : Type*} [Field R] [CharZero R] (f : ℤ → R) (d : ℕ) :
    (∀ n : ℤ, (fwdDiff (1 : ℤ))^[d + 1] f n = 0) ↔
      ∃ p : Polynomial R, p.natDegree ≤ d ∧ ∀ n : ℤ, f n = p.eval (n : R) := by p2m_exact_reverting @_root_.P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.solution
