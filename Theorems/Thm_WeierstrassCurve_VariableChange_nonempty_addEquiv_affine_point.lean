import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

theorem WeierstrassCurve.VariableChange.nonempty_addEquiv_affine_point
    {L : Type*} [Field L] [DecidableEq L] (W : WeierstrassCurve L)
    (C : WeierstrassCurve.VariableChange L) :
    Nonempty ((C • W).toAffine.Point ≃+ W.toAffine.Point) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point.solution
