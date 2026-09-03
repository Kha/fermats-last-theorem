import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff

open WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors
theorem WeierstrassCurve.Affine.CoordinateRing.isPrincipal_prod_XYIdeal_zpow_iff {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {ι : Type*} (s : Finset ι) (x y : ι → F) (h : ∀ i, W.toAffine.Nonsingular (x i) (y i)) (m : ι → ℤ) : ((∏ i ∈ s, CoordinateRing.XYIdeal' (h i) ^ m i : (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ) : Submodule W.toAffine.CoordinateRing W.toAffine.FunctionField).IsPrincipal ↔ ∑ i ∈ s, m i • Point.some (x i) (y i) (h i) = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff.solution
