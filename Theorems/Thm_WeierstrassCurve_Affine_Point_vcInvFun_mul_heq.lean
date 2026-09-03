import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.Point.vcInvFun_mul_heq
    {K : Type*} [Field K] [DecidableEq K]
    (C C' : VariableChange K) (W : WeierstrassCurve.Affine K) (T : W.Point) :
    HEq (Point.vcInvFun (C * C') W T) (Point.vcInvFun C (C' • W) (Point.vcInvFun C' W T)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq.solution
