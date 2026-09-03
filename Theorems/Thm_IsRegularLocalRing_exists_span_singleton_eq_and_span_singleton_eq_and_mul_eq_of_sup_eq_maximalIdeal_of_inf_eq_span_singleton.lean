import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_span_singleton_eq_and_span_singleton_eq_and_mul_eq_of_sup_eq_maximalIdeal_of_inf_eq_span_singleton

set_option autoImplicit false

theorem IsRegularLocalRing.exists_span_singleton_eq_and_span_singleton_eq_and_mul_eq_of_sup_eq_maximalIdeal_of_inf_eq_span_singleton
    {R : Type*} [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : P ≠ IsLocalRing.maximalIdeal R) (hQ : Q ≠ IsLocalRing.maximalIdeal R)
    (hsup : P ⊔ Q = IsLocalRing.maximalIdeal R)
    (π : R) (hπ : π ≠ 0) (hinf : P ⊓ Q = Ideal.span {π}) :
    ∃ (u v : R) (c : Rˣ), P = Ideal.span {u} ∧ Q = Ideal.span {v} ∧ u * v = c * π := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_span_singleton_eq_and_span_singleton_eq_and_mul_eq_of_sup_eq_maximalIdeal_of_inf_eq_span_singleton.solution
