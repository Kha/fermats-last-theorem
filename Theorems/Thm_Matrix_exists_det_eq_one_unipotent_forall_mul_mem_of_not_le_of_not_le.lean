import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le

set_option autoImplicit false

theorem Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le
    {F : Type*} [Field F] (I₀ I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤)
    (h₀ : ¬ I₀ ≤ I) (h₀' : ¬ I₀ ≤ I') :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧
      (∀ A ∈ I₀, A * g ∈ I₀) ∧ ∀ A ∈ I, A * g ∈ I' := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le.solution
