import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_MvPolynomial_finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt
    (n m : ℕ) (hm : 1 ≤ m) (k : Type) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (a : Fin (n + 1) → k)
    (hgrowth : Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) (m + 1)) =
      Nat.macaulayPow m (Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) m)))
    (hsum : Nat.macaulayPow m (Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) m)) +
        Module.finrank k (piece J m) = Nat.macaulayPow m (Module.finrank k (piece J m))) :
    let J' : Ideal (MvPolynomial (Fin (n + 1)) k) :=
      Ideal.span {f | f ∈ J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)} ∧ f.IsHomogeneous m}
    Module.finrank k (piece J' (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J' m)) ∧
    (0 < Module.finrank k (piece J m) → Module.finrank k (piece J' m) < Module.finrank k (piece J m)) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt.solution
