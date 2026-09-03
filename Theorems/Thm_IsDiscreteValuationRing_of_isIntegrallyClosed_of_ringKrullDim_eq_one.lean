import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one

theorem IsDiscreteValuationRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one.solution
