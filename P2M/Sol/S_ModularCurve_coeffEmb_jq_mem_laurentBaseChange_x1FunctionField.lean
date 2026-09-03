import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import P2M.Util
namespace P2MW.S_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField

set_option autoImplicit false

theorem solution
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] :
    ModularCurve.coeffEmb L ModularCurve.jq ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N) := by
  apply ModularCurve.coeffEmb_mem_laurentBaseChange
  rw [← ModularCurve.jqModC_rat]
  show ModularCurve.jqModC ℚ ∈
    IntermediateField.adjoin ℚ (ModularCurve.intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 N))
  exact IntermediateField.subset_adjoin ℚ _
    (ModularCurve.jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 N))
