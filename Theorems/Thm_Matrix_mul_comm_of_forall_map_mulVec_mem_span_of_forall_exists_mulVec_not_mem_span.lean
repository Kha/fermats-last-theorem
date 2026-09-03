import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span

set_option autoImplicit false

theorem Matrix.mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span
    {F F' : Type*} [Field F] [Field F'] (e : F →+* F') {ι : Type*}
    (M : ι → Matrix (Fin 2) (Fin 2) F)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ i, (M i).mulVec v ∉ F ∙ v)
    (u : Fin 2 → F') (hu : u ≠ 0) (hstab : ∀ i, ((M i).map e).mulVec u ∈ F' ∙ u) :
    ∀ i j, M i * M j = M j * M i := by p2m_exact_reverting @_root_.P2MW.S_Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span.solution
