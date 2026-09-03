import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_exists_mem_forall_of_finset_of_directed

open CategoryTheory
theorem Submodule.exists_mem_forall_of_finset_of_directed {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ι : Type*} [Nonempty ι] (T : ι → Submodule k V) (hdir : Directed (· ≤ ·) T)
    (s : Finset V) (hs : ∀ x ∈ s, ∃ i, x ∈ T i) : ∃ j, ∀ x ∈ s, x ∈ T j := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_mem_forall_of_finset_of_directed.solution
