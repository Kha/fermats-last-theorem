import Mathlib
import P2M.Util
import P2M.Sol.S_mem_nonZeroDivisors_of_forall_isMaximal_algebraMap_adicCompletion_mem

set_option autoImplicit false

theorem mem_nonZeroDivisors_of_forall_isMaximal_algebraMap_adicCompletion_mem
    (B : Type) [CommRing B] [IsNoetherianRing B] (b : B)
    (h : ∀ (𝔪 : Ideal B), 𝔪.IsMaximal →
      algebraMap B (AdicCompletion 𝔪 B) b ∈ nonZeroDivisors (AdicCompletion 𝔪 B)) :
    b ∈ nonZeroDivisors B := by p2m_exact_reverting @_root_.P2MW.S_mem_nonZeroDivisors_of_forall_isMaximal_algebraMap_adicCompletion_mem.solution
