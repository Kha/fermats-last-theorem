import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

open NumberField IsDedekindDomain
theorem AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn (F : Type) [Field F] [NumberField F]
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : AutomorphicForm.IsFactorizableTestFn F f) :
    Continuous f ∧ HasCompactSupport f := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn.solution
