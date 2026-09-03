import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le
    (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      Nat.macaulayPow d (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) d)) +
          Module.finrank K (piece J d) ≤
        Nat.macaulayPow d (Module.finrank K (piece J d)) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.solution
