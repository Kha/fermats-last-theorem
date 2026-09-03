import Definitions.Def_ModelTransfer_ClearedData
import Theorems.Thm_FLT_ModelTransfer_exists_clearedData_not_dvd
import Theorems.Thm_FLT_ModelTransfer_reducedChange_smul_reductionMod
import Theorems.Thm_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq
import P2M.Util
namespace P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open WeierstrassCurve FLT.ModelTransfer

theorem solution {V W : WeierstrassCurve ℤ}
    {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by
  classical
  obtain ⟨D, hD⟩ := exists_clearedData_not_dvd hq hq2 hq3 hC hV hW
  haveI : Fact q.Prime := ⟨hq⟩
  have hred := reducedChange_smul_reductionMod hC D hD
  have hcard : (W.reductionMod q).card = (V.reductionMod q).card :=
    card_eq_of_variableChange_smul_eq hred
  simp only [WeierstrassCurve.apOfModel, WeierstrassCurve.traceOfFrobenius, hcard]
