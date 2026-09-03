import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isOpen_principalLevel

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isOpen_principalLevel
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    IsOpen ((principalLevel (𝓞 F) F N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isOpen_principalLevel.solution
