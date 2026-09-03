import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Smooth_isIntegrallyClosed_quotient_of_mem_minimalPrimes

universe u

theorem Algebra.Smooth.isIntegrallyClosed_quotient_of_mem_minimalPrimes
    (K : Type u) [Field K] (S : Type u) [CommRing S] [Algebra K S] [Algebra.Smooth K S]
    (𝔭 : Ideal S) (h𝔭 : 𝔭 ∈ minimalPrimes S) :
    IsIntegrallyClosed (S ⧸ 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Smooth_isIntegrallyClosed_quotient_of_mem_minimalPrimes.solution
