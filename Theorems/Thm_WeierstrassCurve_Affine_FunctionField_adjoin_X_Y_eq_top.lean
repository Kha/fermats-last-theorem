import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_FunctionField_adjoin_X_Y_eq_top

theorem WeierstrassCurve.Affine.FunctionField.adjoin_X_Y_eq_top {K : Type*} [Field K] (W : WeierstrassCurve K) : IntermediateField.adjoin K {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)), algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_FunctionField_adjoin_X_Y_eq_top.solution
