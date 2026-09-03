import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq

set_option autoImplicit false

theorem IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) = ringKrullDim R := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq.solution
