import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_finset_span_eq_top_of_forall_prime_exists_not_mem

set_option autoImplicit false

theorem Ideal.exists_finset_span_eq_top_of_forall_prime_exists_not_mem
    {S : Type} [CommRing S] (P : S → Prop)
    (h : ∀ 𝔭 : PrimeSpectrum S, ∃ g : S, g ∉ 𝔭.asIdeal ∧ P g) :
    ∃ (k : ℕ) (g : Fin k → S), Ideal.span (Set.range g) = ⊤ ∧ ∀ i, P (g i) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_finset_span_eq_top_of_forall_prime_exists_not_mem.solution
