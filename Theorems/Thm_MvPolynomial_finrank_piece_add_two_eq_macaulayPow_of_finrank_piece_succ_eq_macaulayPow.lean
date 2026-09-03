import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow

set_option autoImplicit false

open MvPolynomial hiding finrank_piece_succ_le_macaulayPow exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow open AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    Module.finrank K (piece J (m + 2)) = Nat.macaulayPow (m + 1) (Module.finrank K (piece J (m + 1))) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow.solution
