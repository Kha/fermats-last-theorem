import Mathlib
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ) =
      ModularCurve.xHFunctionField (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap.solution
