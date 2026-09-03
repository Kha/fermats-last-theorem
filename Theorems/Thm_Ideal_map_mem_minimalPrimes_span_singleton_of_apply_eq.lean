import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_map_mem_minimalPrimes_span_singleton_of_apply_eq

set_option autoImplicit false

theorem Ideal.map_mem_minimalPrimes_span_singleton_of_apply_eq
    {S : Type*} [CommRing S] (γ : S ≃+* S) (π : S) (hγπ : γ π = π)
    {P : Ideal S} (hP : P ∈ (Ideal.span {π}).minimalPrimes) :
    P.map (γ : S →+* S) ∈ (Ideal.span {π}).minimalPrimes := by p2m_exact_reverting @_root_.P2MW.S_Ideal_map_mem_minimalPrimes_span_singleton_of_apply_eq.solution
