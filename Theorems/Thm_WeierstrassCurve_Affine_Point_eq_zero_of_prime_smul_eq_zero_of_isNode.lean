import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_eq_zero_of_prime_smul_eq_zero_of_isNode

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode {k : Type*} [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) (x₀ y₀ : k) (he : W.toAffine.Equation x₀ y₀) (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hnode : W.b₂ + 12 * x₀ ≠ 0) (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_eq_zero_of_prime_smul_eq_zero_of_isNode.solution
