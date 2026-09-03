import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Mathlib.Data.Complex.Basic
import P2M.Util
namespace P2MW.S_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange

theorem solution (N : ℕ) [NeZero N]
    (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb ℂ x ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    x ∈ ModularCurve.modularFunctionFieldFull N :=
  ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) x hx
