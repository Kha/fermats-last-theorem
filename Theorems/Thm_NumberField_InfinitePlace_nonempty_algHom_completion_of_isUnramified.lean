import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_nonempty_algHom_completion_of_isUnramified

set_option autoImplicit false

open NumberField

theorem NumberField.InfinitePlace.nonempty_algHom_completion_of_isUnramified
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) (w : InfinitePlace L) (hw : w.comap (algebraMap K L) = v)
    (hun : w.IsUnramified K) :
    Nonempty (L →ₐ[K] v.Completion) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_nonempty_algHom_completion_of_isUnramified.solution
