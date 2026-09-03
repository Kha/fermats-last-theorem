import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_adelicHeight_diagOne
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe AutomorphicForm.cpowChar_apply_val

set_option autoImplicit false

open NumberField

theorem NumberField.AdelicHeight.adelicHeight_diagOne (F : Type) [Field F] [NumberField F]
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.AdelicHeight.adelicHeight F (NumberField.AdelicLevel.diagOne t : AutomorphicForm.AdelicGL2 (𝓞 F) F) =
      NumberField.TateGlobal.ideleNorm F t := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_adelicHeight_diagOne.solution
