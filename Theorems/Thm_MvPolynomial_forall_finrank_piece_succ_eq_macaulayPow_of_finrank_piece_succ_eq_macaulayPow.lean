import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow

set_option autoImplicit false

open MvPolynomial hiding finrank_piece_succ_le_macaulayPow exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow finrank_piece_eq_of_maximal_growth finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow open AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∀ e : ℕ, m ≤ e → Module.finrank K (piece J (e + 1)) = Nat.macaulayPow e (Module.finrank K (piece J e)) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow.solution
