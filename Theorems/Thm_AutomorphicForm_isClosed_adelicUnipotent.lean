import Definitions.Def_AutomorphicForm_UnipotentQuotient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isClosed_adelicUnipotent

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.isClosed_adelicUnipotent (K : Type) [Field K] [NumberField K] :
    IsClosed ((adelicUnipotent K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isClosed_adelicUnipotent.solution
