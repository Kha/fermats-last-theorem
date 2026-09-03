import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet

theorem WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) : ∃ (u v : Polynomial k) (B : Set k), IsCoprime u v ∧ B.Finite ∧ ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B → ∃ (x' y' : k) (h' : (W₂.baseChange k).toAffine.Nonsingular x' y'), α (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x' y' h' ∧ x' * v.eval x = u.eval x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet.solution
