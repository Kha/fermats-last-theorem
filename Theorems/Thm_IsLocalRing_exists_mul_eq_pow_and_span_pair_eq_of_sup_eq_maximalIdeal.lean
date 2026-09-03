import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal

theorem IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A]
    {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A)
    {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hQP : ¬ Q ≤ P)
    (hPQ : P ⊔ Q = IsLocalRing.maximalIdeal A)
    {a b : A} (ha : Ideal.span {a, ϖ} = P) (hb : Ideal.span {b, ϖ} = Q)
    (hab : a * b ∈ Ideal.span {ϖ})
    {n : ℕ} {t t' : A} (htQ : t ∉ Q) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (htt' : t * t' = ϖ ^ n) :
    ∃ (e : ℕ) (u v : A), 1 ≤ e ∧ e ≤ n ∧ u * v = ϖ ^ e ∧
      Ideal.span {u, ϖ} = P ∧ Ideal.span {v, ϖ} = Q := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal.solution
