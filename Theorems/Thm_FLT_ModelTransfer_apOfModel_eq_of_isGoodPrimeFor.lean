import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor
attribute [-simp] FLT.ModelTransfer.reducedChange_r FLT.ModelTransfer.reducedChange_t FLT.ModelTransfer.reducedChange_s FLT.ModelTransfer.ClearedData.mk.injEq FLT.ModelTransfer.reducedChange_u FLT.ModelTransfer.ClearedData.mk.sizeOf_spec FLT.ModelTransfer.reducedChange_u_inv WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open WeierstrassCurve
namespace FLT.ModelTransfer
theorem apOfModel_eq_of_isGoodPrimeFor {V W : WeierstrassCurve ℤ}
    {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by p2m_exact_reverting @_root_.P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor.solution
end FLT.ModelTransfer
