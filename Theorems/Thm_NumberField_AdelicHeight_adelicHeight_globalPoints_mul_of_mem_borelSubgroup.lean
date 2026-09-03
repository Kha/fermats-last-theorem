import Mathlib
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup

open scoped NumberField

theorem NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup
    (F : Type) [Field F] [NumberField F]
    {γ : Matrix.GeneralLinearGroup (Fin 2) F} (hγ : γ ∈ AutomorphicForm.borelSubgroup F)
    (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g)
      = NumberField.AdelicHeight.adelicHeight F g := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup.solution
