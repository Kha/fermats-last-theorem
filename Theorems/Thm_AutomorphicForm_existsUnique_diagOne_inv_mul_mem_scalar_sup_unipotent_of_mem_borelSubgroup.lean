import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup

set_option autoImplicit false

open AutomorphicForm NumberField.AdelicLevel

theorem AutomorphicForm.existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup
    (K : Type*) [Field K] (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    ∃! a : Kˣ, (diagOne a)⁻¹ * b ∈
      (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom).range ⊔
        (unipotentGL2Hom (R := K)).range := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup.solution
