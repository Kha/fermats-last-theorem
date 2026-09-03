import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization

theorem IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization.solution
