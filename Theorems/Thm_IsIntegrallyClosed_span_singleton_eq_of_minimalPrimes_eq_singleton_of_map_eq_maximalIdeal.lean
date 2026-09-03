import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_span_singleton_eq_of_minimalPrimes_eq_singleton_of_map_eq_maximalIdeal

set_option autoImplicit false

theorem IsIntegrallyClosed.span_singleton_eq_of_minimalPrimes_eq_singleton_of_map_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (x : A) (P : Ideal A) [P.IsPrime]
    (hmin : (Ideal.span {x}).minimalPrimes = {P})
    (hunif : Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    Ideal.span {x} = P := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_span_singleton_eq_of_minimalPrimes_eq_singleton_of_map_eq_maximalIdeal.solution
