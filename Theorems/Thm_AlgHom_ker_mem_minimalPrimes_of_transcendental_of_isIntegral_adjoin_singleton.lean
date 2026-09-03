import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton

set_option autoImplicit false

theorem AlgHom.ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton
    (A₀ R K : Type) [CommRing A₀] [CommRing R] [Field K] [Algebra A₀ R] [Algebra A₀ K]
    (j₀ : R) (ι : R →ₐ[A₀] K) (htr : Transcendental A₀ (ι j₀))
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A₀ {j₀}) R) :
    RingHom.ker ι.toRingHom ∈ (⊥ : Ideal R).minimalPrimes := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton.solution
