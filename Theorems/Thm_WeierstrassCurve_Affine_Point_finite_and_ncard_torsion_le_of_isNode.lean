import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_finite_and_ncard_torsion_le_of_isNode

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.finite_and_ncard_torsion_le_of_isNode {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) (x₀ y₀ : k) (he : W.toAffine.Equation x₀ y₀) (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hnode : W.b₂ + 12 * x₀ ≠ 0) {n : ℕ} (hn : 0 < n) : {P : W.toAffine.Point | n • P = 0}.Finite ∧ {P : W.toAffine.Point | n • P = 0}.ncard ≤ n := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_finite_and_ncard_torsion_le_of_isNode.solution
