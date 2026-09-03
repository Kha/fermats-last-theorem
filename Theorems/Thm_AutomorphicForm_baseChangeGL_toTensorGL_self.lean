import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_baseChangeGL_toTensorGL_self

set_option autoImplicit false
open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.baseChangeGL_toTensorGL_self
    (K : Type) [Field K] [NumberField K] (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    AutomorphicForm.baseChangeGL K K (AutomorphicForm.toTensorGL K K (AdeleRing (𝓞 K) K) x) = x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_baseChangeGL_toTensorGL_self.solution
