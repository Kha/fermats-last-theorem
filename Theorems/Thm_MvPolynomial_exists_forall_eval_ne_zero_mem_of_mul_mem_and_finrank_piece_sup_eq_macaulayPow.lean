import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow

set_option autoImplicit false

p2m_open "MvPolynomial~finrank_piece_succ_le_macaulayPow~exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le AlgebraicGeometry.HilbertFunctor"

theorem MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      (∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m → (∑ i, C (a i) * X i) * f ∈ J → f ∈ J) ∧
      Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) (m + 1)) =
        Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) ∧
      Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) +
          Module.finrank K (piece J m) = Nat.macaulayPow m (Module.finrank K (piece J m)) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow.solution
