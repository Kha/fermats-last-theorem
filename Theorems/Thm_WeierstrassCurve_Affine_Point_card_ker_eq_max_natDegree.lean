import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_card_ker_eq_max_natDegree

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.card_ker_eq_max_natDegree {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] (W : WeierstrassCurve k) [W.IsElliptic] (ψ : W.toAffine.Point →+ W.toAffine.Point) {B : Set W.toAffine.Point} (hB : B.Finite) {g h : Polynomial k} (hgh : IsCoprime g h) (hsep : Polynomial.derivative g * h - g * Polynomial.derivative h ≠ 0) (hker : ∀ {x y : k} (hP : W.toAffine.Nonsingular x y), Point.some x y hP ∉ B → h.eval x ≠ 0 → ψ (Point.some x y hP) ≠ 0) (hx : ∀ {x y : k} (hP : W.toAffine.Nonsingular x y) {x' y' : k} (hP' : W.toAffine.Nonsingular x' y'), Point.some x y hP ∉ B → ψ (Point.some x y hP) = Point.some x' y' hP' → x' * h.eval x = g.eval x) : Nat.card ψ.ker = max g.natDegree h.natDegree := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_card_ker_eq_max_natDegree.solution
