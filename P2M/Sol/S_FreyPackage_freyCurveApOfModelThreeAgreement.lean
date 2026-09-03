import Definitions.Def_FreyPackage_RouteAReversePinSeam
import Theorems.Thm_FLT_ModelTransfer_apOfModel_eq_of_isIntegralModelOf_odd
import Theorems.Thm_FreyCurve_freyCurveInt_apOfModel_three
import Theorems.Thm_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve
import Theorems.Thm_FreyPackage_dvd_freyCurveInt_discr_iff
import Theorems.Thm_FreyPackage_freyCurveInt_map
import P2M.Util
namespace P2MW.S_FreyPackage_freyCurveApOfModelThreeAgreement
attribute [-simp] FLT.ModelTransfer.reducedChange_r FLT.ModelTransfer.reducedChange_t FLT.ModelTransfer.reducedChange_s FLT.ModelTransfer.ClearedData.mk.injEq FLT.ModelTransfer.reducedChange_u FLT.ModelTransfer.ClearedData.mk.sizeOf_spec FLT.ModelTransfer.reducedChange_u_inv WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false

open WeierstrassCurve

theorem solution (P : FreyPackage) : P.FreyCurveApOfModelThreeAgreement := by
  intro W hWmodel hgoodW

  have hVmodel : (FreyPackage.freyCurveInt P).IsIntegralModelOf P.freyCurve :=
    ⟨1, by rw [one_smul, FreyPackage.freyCurveInt_map]⟩

  have hgoodV : (FreyPackage.freyCurveInt P).IsGoodPrimeFor 3 := fun h3 =>
    FreyPackage.not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve P hWmodel Nat.prime_three
      ((FreyPackage.dvd_freyCurveInt_discr_iff P Nat.prime_three).mp h3) hgoodW

  have hagree : W.apOfModel 3 = (FreyPackage.freyCurveInt P).apOfModel 3 :=
    FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf_odd hVmodel hWmodel Nat.prime_three
      (by norm_num) hgoodV hgoodW
  rw [hagree]
  exact FreyCurve.freyCurveInt_apOfModel_three P hgoodV
