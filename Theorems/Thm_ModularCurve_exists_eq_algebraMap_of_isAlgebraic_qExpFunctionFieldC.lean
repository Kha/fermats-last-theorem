import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve

theorem ModularCurve.exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
    (Γ : Subgroup SL(2, ℤ)) (x : ↥(qExpFunctionFieldC ℚ Γ)) (hx : IsAlgebraic ℚ x) :
    ∃ c : ℚ, x = algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC.solution
