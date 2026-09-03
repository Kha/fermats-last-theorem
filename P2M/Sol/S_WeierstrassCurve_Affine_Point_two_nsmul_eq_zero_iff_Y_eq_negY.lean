import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import P2M.Util
namespace P2MW.S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY

open WeierstrassCurve.Affine.Point
theorem solution {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y) :
    2 • (some _ _ h : W.Point) = 0 ↔ y = W.negY x y := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, neg_some]
  exact ⟨fun hP => (some.inj hP).right, fun hy => by simp only [some.injEq]; exact ⟨trivial, hy⟩⟩
