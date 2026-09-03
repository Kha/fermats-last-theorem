import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
set_option autoImplicit false

theorem IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le.solution
