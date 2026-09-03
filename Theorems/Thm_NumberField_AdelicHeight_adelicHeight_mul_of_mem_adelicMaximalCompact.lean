import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField NumberField.AdelicHeight AutomorphicForm

theorem NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact
    (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ AutomorphicForm.adelicMaximalCompact F) :
    adelicHeight F (g * k) = adelicHeight F g := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact.solution
