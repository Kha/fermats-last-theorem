import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker (K : Type*) [Field K] (M₀ q : ℕ)
    [NeZero M₀] [NeZero q] (h : Nat.Coprime M₀ q) :
    ModularCurve.x1x0FunctionFieldC K M₀ q =
      ModularCurve.xHFunctionFieldC K (M₀ * q) (ZMod.unitsMap (dvd_mul_right M₀ q)).ker := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker.solution
