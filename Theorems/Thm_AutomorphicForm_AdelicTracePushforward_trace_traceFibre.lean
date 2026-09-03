import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_AdelicTracePushforward_trace_traceFibre

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.AdelicTracePushforward.trace_traceFibre
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (r : AdeleRing (𝓞 K) K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    letI := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra
    Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L)
      (AutomorphicForm.AdelicTracePushforward.traceFibre K L r w) = r := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_AdelicTracePushforward_trace_traceFibre.solution
