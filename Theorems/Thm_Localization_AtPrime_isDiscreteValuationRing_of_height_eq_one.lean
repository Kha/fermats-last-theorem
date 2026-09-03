import Mathlib
import P2M.Util
import P2M.Sol.S_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one

theorem Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by p2m_exact_reverting @_root_.P2MW.S_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one.solution
