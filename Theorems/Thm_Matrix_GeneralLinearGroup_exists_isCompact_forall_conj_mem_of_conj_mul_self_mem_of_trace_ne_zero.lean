import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero
    {𝕜 : Type*} [RCLike 𝕜]
    (T : Set (GL (Fin 2) 𝕜)) (hT : IsCompact T)
    (hTtr : ∀ t ∈ T, Matrix.trace ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) ≠ 0)
    (B : Set (GL (Fin 2) 𝕜)) (hB : IsCompact B) :
    ∃ B' : Set (GL (Fin 2) 𝕜), IsCompact B' ∧
      ∀ t ∈ T, ∀ x : GL (Fin 2) 𝕜, x⁻¹ * (t * t) * x ∈ B → x⁻¹ * t * x ∈ B' := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero.solution
