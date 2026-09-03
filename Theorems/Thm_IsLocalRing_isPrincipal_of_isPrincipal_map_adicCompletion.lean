import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isPrincipal_of_isPrincipal_map_adicCompletion
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

theorem IsLocalRing.isPrincipal_of_isPrincipal_map_adicCompletion
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (h : (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).IsPrincipal) :
    I.IsPrincipal := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isPrincipal_of_isPrincipal_map_adicCompletion.solution
