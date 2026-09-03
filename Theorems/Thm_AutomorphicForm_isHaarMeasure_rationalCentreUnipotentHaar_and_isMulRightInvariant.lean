import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
    (K : Type) [Field K] [NumberField K] :
    (rationalCentreUnipotentHaar K).IsHaarMeasure ∧ (rationalCentreUnipotentHaar K).IsMulRightInvariant := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant.solution
