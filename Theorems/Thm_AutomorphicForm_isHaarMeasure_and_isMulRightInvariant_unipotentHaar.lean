import Definitions.Def_AutomorphicForm_UnipotentQuotient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isHaarMeasure_and_isMulRightInvariant_unipotentHaar (K : Type*) [Field K]
    [NumberField K] :
    (AutomorphicForm.unipotentHaar K).IsHaarMeasure ∧
      (AutomorphicForm.unipotentHaar K).IsMulRightInvariant := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar.solution
