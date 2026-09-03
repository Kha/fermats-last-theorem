import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
import P2M.Util
namespace P2MW.S_IsRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    (h : ringKrullDim R = 1) : IsRegularLocalRing R := by
  haveI := IsDiscreteValuationRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one R h
  infer_instance
