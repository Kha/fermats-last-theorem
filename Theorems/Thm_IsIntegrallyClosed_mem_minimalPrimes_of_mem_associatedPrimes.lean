import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes

theorem IsIntegrallyClosed.mem_minimalPrimes_of_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ associatedPrimes A (A ⧸ Ideal.span {x})) :
    P ∈ (Ideal.span {x}).minimalPrimes := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes.solution
