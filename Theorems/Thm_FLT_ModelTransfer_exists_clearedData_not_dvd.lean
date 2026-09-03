import Definitions.Def_ModelTransfer_ClearedData
import P2M.Util
import P2M.Sol.S_FLT_ModelTransfer_exists_clearedData_not_dvd

open WeierstrassCurve
namespace FLT.ModelTransfer
theorem exists_clearedData_not_dvd {V W : WeierstrassCurve ℤ} {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    ∃ D : FLT.ModelTransfer.ClearedData C, ¬ q ∣ D.N := by p2m_exact_reverting @_root_.P2MW.S_FLT_ModelTransfer_exists_clearedData_not_dvd.solution
end FLT.ModelTransfer
