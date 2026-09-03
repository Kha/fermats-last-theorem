import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuous_unipotentGL2

theorem AutomorphicForm.continuous_unipotentGL2 {R : Type*} [CommRing R] [TopologicalSpace R]
    [ContinuousNeg R] : Continuous fun x : R => AutomorphicForm.unipotentGL2 x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_unipotentGL2.solution
