import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow

set_option autoImplicit false

p2m_open "MvPolynomial~exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le AlgebraicGeometry.HilbertFunctor"

theorem MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      ∀ k : ℕ, m ≤ k → ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous k →
        (∑ i, C (a i) * X i) * f ∈ J → f ∈ J := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.solution
