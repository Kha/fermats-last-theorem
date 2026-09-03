import Definitions.Def_AutomorphicForm_WeylSelectors
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WeylIntegrable_Dy_pos

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.Dy_pos (F : Type) [Field F] [NumberField F]
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) : 0 < Dy F x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WeylIntegrable_Dy_pos.solution
