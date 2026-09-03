import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_isRegularLocalRing_localization_atPrime_of_ringKrullDim_eq_one

universe u

theorem IsIntegrallyClosed.isRegularLocalRing_localization_atPrime_of_ringKrullDim_eq_one
    {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsIntegrallyClosed T]
    (p : Ideal T) [p.IsPrime] (h : ringKrullDim (Localization.AtPrime p) = 1) :
    IsRegularLocalRing (Localization.AtPrime p) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isRegularLocalRing_localization_atPrime_of_ringKrullDim_eq_one.solution
