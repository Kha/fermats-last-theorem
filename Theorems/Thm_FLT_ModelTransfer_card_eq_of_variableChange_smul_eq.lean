import Definitions.Def_FLTPrelim_Modularity
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import P2M.Util
import P2M.Sol.S_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open WeierstrassCurve
namespace FLT.ModelTransfer
theorem card_eq_of_variableChange_smul_eq {K : Type*} [Field K] [DecidableEq K]
    {X Y : WeierstrassCurve K} {E : WeierstrassCurve.VariableChange K} (h : E • X = Y) :
    Y.card = X.card := by p2m_exact_reverting @_root_.P2MW.S_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq.solution
end FLT.ModelTransfer
