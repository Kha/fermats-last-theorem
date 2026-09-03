import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton

set_option autoImplicit false

theorem Ideal.exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
    (I : Ideal R) (π : S) (hI : I.map (algebraMap R S) = Ideal.span {π}) (hπ : π ∈ nonZeroDivisors S) :
    ∃ g ∈ I, I.map (algebraMap R S) = Ideal.span {algebraMap R S g} ∧ algebraMap R S g ∈ nonZeroDivisors S := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton.solution
