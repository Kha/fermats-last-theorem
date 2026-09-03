import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn

open NumberField

theorem AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hf : IsFactorizableTestFn K f)
    (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    IsFactorizableTestFn K (fun y => f (t⁻¹ * y)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn.solution
