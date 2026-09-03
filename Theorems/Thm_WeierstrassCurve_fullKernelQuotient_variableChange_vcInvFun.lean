import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_fullKernelQuotient_variableChange_vcInvFun
attribute [-simp] WeierstrassCurve.vcInvEmbedding_apply

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.fullKernelQuotient_variableChange_vcInvFun
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (C : VariableChange F)
    (Q : W.toAffine.Point) {N : ℕ} (hQ : addOrderOf Q = N) :
    (C • W).fullKernelQuotient (Point.vcInvFun C W.toAffine Q) N =
      C • W.fullKernelQuotient Q N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_fullKernelQuotient_variableChange_vcInvFun.solution
