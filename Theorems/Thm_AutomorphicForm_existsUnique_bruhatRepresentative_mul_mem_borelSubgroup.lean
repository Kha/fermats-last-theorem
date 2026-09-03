import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_WeylIntertwining
import P2M.Util
import P2M.Sol.S_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
    (K : Type*) [Field K] (γ : GL (Fin 2) K) :
    ∃! o : Option K, (o.elim 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup.solution
