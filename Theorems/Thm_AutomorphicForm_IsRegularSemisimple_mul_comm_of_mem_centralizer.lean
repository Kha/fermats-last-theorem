import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsRegularSemisimple_mul_comm_of_mem_centralizer

set_option autoImplicit false

theorem AutomorphicForm.IsRegularSemisimple.mul_comm_of_mem_centralizer
    (A : Type) [CommRing A] (g : GL (Fin 2) A) (hg : AutomorphicForm.IsRegularSemisimple g)
    (s t : GL (Fin 2) A) (hs : s ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) :
    s * t = t * s := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsRegularSemisimple_mul_comm_of_mem_centralizer.solution
