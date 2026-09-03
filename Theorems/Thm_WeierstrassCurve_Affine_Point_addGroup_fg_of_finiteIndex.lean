import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex

theorem WeierstrassCurve.Affine.Point.addGroup_fg_of_finiteIndex (W : WeierstrassCurve.Affine ℚ) (hΔ : W.Δ ≠ 0) (hweak : (nsmulAddMonoidHom 2 : W.Point →+ W.Point).range.FiniteIndex) : AddGroup.FG W.Point := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.solution
