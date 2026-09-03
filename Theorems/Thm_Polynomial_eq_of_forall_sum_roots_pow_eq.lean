import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_eq_of_forall_sum_roots_pow_eq

set_option autoImplicit false

theorem Polynomial.eq_of_forall_sum_roots_pow_eq {K : Type*} [Field K] [CharZero K]
    (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic) (hPs : P.Splits) (hQs : Q.Splits)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ n : ℕ, 0 < n →
      (P.roots.map (fun z => z ^ n)).sum = (Q.roots.map (fun z => z ^ n)).sum) :
    P = Q := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_eq_of_forall_sum_roots_pow_eq.solution
