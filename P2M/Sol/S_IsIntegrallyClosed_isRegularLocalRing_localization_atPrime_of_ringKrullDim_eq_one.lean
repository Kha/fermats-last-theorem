import Mathlib
import Theorems.Thm_IsRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
import P2M.Util
namespace P2MW.S_IsIntegrallyClosed_isRegularLocalRing_localization_atPrime_of_ringKrullDim_eq_one

universe u

theorem solution
    {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsIntegrallyClosed T]
    (p : Ideal T) [p.IsPrime] (h : ringKrullDim (Localization.AtPrime p) = 1) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have hle : p.primeCompl ≤ nonZeroDivisors T := Ideal.primeCompl_le_nonZeroDivisors p
  haveI : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl hle
  haveI : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime p) hle
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  exact IsRegularLocalRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one _ h
