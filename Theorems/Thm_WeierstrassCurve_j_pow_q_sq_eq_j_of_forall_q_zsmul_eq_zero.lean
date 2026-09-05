module

public import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
    {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] (q : ℕ) [Fact q.Prime]
    [CharP F q] (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0) :
    E.j ^ (q ^ 2) = E.j := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero.solution
