import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_mem_forall_not_mem_of_forall_not_le

set_option autoImplicit false

theorem Ideal.exists_mem_forall_not_mem_of_forall_not_le
    {R : Type*} [CommRing R] (J : Ideal R) (S : Finset (Ideal R))
    (hS : ∀ P ∈ S, P.IsPrime) (h : ∀ P ∈ S, ¬ J ≤ P) :
    ∃ i ∈ J, ∀ P ∈ S, i ∉ P := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_mem_forall_not_mem_of_forall_not_le.solution
