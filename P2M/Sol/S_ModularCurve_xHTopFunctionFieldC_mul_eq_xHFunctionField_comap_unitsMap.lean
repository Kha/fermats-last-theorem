import Mathlib
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
import P2M.Util
namespace P2MW.S_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ) =
      ModularCurve.xHFunctionField (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) := by
  show ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) =
    ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))))
  rw [CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap]
