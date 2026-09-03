import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor
import P2M.Util
namespace P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isIntegralModelOf
attribute [-simp] FLT.ModelTransfer.reducedChange_r FLT.ModelTransfer.reducedChange_t FLT.ModelTransfer.reducedChange_s FLT.ModelTransfer.ClearedData.mk.injEq FLT.ModelTransfer.reducedChange_u FLT.ModelTransfer.ClearedData.mk.sizeOf_spec FLT.ModelTransfer.reducedChange_u_inv WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open WeierstrassCurve

theorem solution {V W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ} {q : ℕ}
    (hVE : V.IsIntegralModelOf E) (hWE : W.IsIntegralModelOf E)
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by
  obtain ⟨C₁, hC₁⟩ := hVE
  obtain ⟨C₂, hC₂⟩ := hWE
  refine FLT.ModelTransfer.apOfModel_eq_of_isGoodPrimeFor hq hq2 hq3 (C := C₂ * C₁⁻¹) ?_ hV hW
  rw [← hC₁, mul_smul, inv_smul_smul, hC₂]
