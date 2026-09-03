import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import P2M.Util
namespace P2MW.S_ModularCurve_full_one_eq

open ModularCurve IntermediateField

noncomputable section

theorem solution : modularFunctionFieldFull 1 = modularFunctionField 1 :=
  (ModularCurve.functionFieldGeneration_iff_full_eq 1).mp functionFieldGeneration_one

end
