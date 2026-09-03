import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

theorem IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) : P.height = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes.solution
