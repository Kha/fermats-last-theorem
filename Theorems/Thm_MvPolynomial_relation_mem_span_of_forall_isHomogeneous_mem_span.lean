import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_relation_mem_span_of_forall_isHomogeneous_mem_span

set_option autoImplicit false

p2m_open "MvPolynomial~exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero"

theorem MvPolynomial.relation_mem_span_of_forall_isHomogeneous_mem_span
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m)
    (hspan : ∀ w : MvPolynomial (Fin (n + 1)) K, w.IsHomogeneous m → w ∈ Submodule.span K (Set.range F))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_relation_mem_span_of_forall_isHomogeneous_mem_span.solution
