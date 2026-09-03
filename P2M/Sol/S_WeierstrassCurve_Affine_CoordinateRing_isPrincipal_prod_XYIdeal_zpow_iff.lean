import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import P2M.Util
namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff

open WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors

theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {ι : Type*} (s : Finset ι) (x y : ι → F) (h : ∀ i, W.toAffine.Nonsingular (x i) (y i)) (m : ι → ℤ) : ((∏ i ∈ s, CoordinateRing.XYIdeal' (h i) ^ m i : (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ) : Submodule W.toAffine.CoordinateRing W.toAffine.FunctionField).IsPrincipal ↔ ∑ i ∈ s, m i • Point.some (x i) (y i) (h i) = 0 := by
  rw [← ClassGroup.mk_eq_one_iff, ← Point.toClass_eq_zero, map_sum]
  have key : Additive.toMul (∑ i ∈ s, Point.toClass (m i • Point.some (x i) (y i) (h i))) =
      ClassGroup.mk W.toAffine.FunctionField (∏ i ∈ s, CoordinateRing.XYIdeal' (h i) ^ m i) := by
    rw [map_prod, toMul_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zsmul, toMul_zsmul, map_zpow, Point.toClass_some]
    rfl
  rw [← key]
  exact Additive.toMul.apply_eq_iff_eq_symm_apply
