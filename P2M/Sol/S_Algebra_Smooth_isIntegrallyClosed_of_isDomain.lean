import Mathlib
import Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
import P2M.Util
namespace P2MW.S_Algebra_Smooth_isIntegrallyClosed_of_isDomain

universe u

theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Smooth R S] : IsIntegrallyClosed S := by

  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  haveI := hp.isPrime
  exact (Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime R S p (Localization.AtPrime p)).2
