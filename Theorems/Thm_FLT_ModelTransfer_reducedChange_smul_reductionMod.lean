import Definitions.Def_ModelTransfer_ClearedData
import P2M.Util
import P2M.Sol.S_FLT_ModelTransfer_reducedChange_smul_reductionMod

open WeierstrassCurve
namespace FLT.ModelTransfer
theorem reducedChange_smul_reductionMod {V W : WeierstrassCurve ℤ} {C : WeierstrassCurve.VariableChange ℚ}
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (D : FLT.ModelTransfer.ClearedData C) {q : ℕ} [Fact q.Prime] (hq : ¬ q ∣ D.N) :
    (FLT.ModelTransfer.reducedChange D hq) • (V.reductionMod q) = W.reductionMod q := by p2m_exact_reverting @_root_.P2MW.S_FLT_ModelTransfer_reducedChange_smul_reductionMod.solution
end FLT.ModelTransfer
