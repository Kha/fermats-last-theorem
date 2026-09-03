import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isClosed_rationalCentreUnipotent

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.isClosed_rationalCentreUnipotent (K : Type) [Field K] [NumberField K] :
    IsClosed (rationalCentreUnipotent K : Set (AdelicGL2 (𝓞 K) K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isClosed_rationalCentreUnipotent.solution
