import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap

theorem WeierstrassCurve.Affine.CoordinateRing.isUnit_iff_eq_algebraMap {F : Type*} [Field F] {W : WeierstrassCurve F} (f : W.toAffine.CoordinateRing) : IsUnit f ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.toAffine.CoordinateRing c := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap.solution
