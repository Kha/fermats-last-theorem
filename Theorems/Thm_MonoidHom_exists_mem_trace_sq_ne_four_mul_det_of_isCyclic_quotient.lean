import Mathlib
import P2M.Util
import P2M.Sol.S_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient

theorem MonoidHom.exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient
    {G : Type*} [Group G] {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) 𝕜)
    (hρ : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] :
    ∃ σ ∈ N, (ρ σ).trace ^ 2 ≠ 4 * (ρ σ).det := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient.solution
