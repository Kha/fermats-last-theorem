import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_nonempty_stabilizer_variableChange_mulEquiv_units_rationalEndSubring
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

theorem WeierstrassCurve.nonempty_stabilizer_variableChange_mulEquiv_units_rationalEndSubring {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve F) [W.IsElliptic] : Nonempty (MulAction.stabilizer (WeierstrassCurve.VariableChange F) W ≃* (WeierstrassCurve.rationalEndSubring k W)ˣ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_nonempty_stabilizer_variableChange_mulEquiv_units_rationalEndSubring.solution
