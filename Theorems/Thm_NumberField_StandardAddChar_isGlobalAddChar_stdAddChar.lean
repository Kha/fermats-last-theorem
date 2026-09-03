import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
import P2M.Sol.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar

open NumberField NumberField.StandardAddChar AutomorphicForm
theorem NumberField.StandardAddChar.isGlobalAddChar_stdAddChar
    (F : Type) [Field F] [NumberField F] :
    IsGlobalAddChar F (stdAddChar F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar.solution
