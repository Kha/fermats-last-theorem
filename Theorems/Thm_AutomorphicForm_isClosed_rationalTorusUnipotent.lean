import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isClosed_rationalTorusUnipotent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isClosed_rationalTorusUnipotent (K : Type) [Field K] [NumberField K] :
    IsClosed (rationalTorusUnipotent K : Set (AdelicGL2 (𝓞 K) K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isClosed_rationalTorusUnipotent.solution
