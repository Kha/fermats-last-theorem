import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.relation_mem_span_of_forall_finrank_piece_succ_le
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m)
    (hmax : ∀ J' : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J' = Ideal.span s) →
      Module.finrank K (piece J' m) = Module.finrank K (piece (Ideal.span (Set.range F)) m) →
      Module.finrank K (piece J' (m + 1)) ≤ Module.finrank K (piece (Ideal.span (Set.range F)) (m + 1)))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.solution
