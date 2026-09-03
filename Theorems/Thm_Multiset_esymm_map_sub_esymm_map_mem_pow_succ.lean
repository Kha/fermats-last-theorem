import Mathlib
import P2M.Util
import P2M.Sol.S_Multiset_esymm_map_sub_esymm_map_mem_pow_succ

set_option autoImplicit false

theorem Multiset.esymm_map_sub_esymm_map_mem_pow_succ
    (A : Type) [CommRing A] (I : Ideal A) (ι : Type) (s : Finset ι) (y z : ι → A)
    (hz : ∀ i ∈ s, z i ∈ I) (hyz : ∀ i ∈ s, y i - z i ∈ I ^ 2) (k : ℕ) :
    (s.val.map y).esymm k - (s.val.map z).esymm k ∈ I ^ (k + 1) := by p2m_exact_reverting @_root_.P2MW.S_Multiset_esymm_map_sub_esymm_map_mem_pow_succ.solution
