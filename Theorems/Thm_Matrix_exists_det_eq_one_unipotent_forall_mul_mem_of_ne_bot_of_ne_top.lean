import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top

set_option autoImplicit false

theorem Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
    {F : Type*} [Field F] (I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤) :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧ g ≠ 1 ∧ ∀ A ∈ I, A * g ∈ I' := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top.solution
