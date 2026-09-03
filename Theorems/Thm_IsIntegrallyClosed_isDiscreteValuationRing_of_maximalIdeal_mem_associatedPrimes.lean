import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes

theorem IsIntegrallyClosed.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [IsLocalRing B]
    {x : B} (hx : x ≠ 0)
    (h : IsLocalRing.maximalIdeal B ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing B := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.solution
