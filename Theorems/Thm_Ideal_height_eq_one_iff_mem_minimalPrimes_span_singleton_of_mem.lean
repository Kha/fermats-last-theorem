import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem

theorem Ideal.height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {x : R} (hx : x ≠ 0) (P : Ideal R) [P.IsPrime] (hxP : x ∈ P) :
    P.height = 1 ↔ P ∈ (Ideal.span {x}).minimalPrimes := by p2m_exact_reverting @_root_.P2MW.S_Ideal_height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem.solution
