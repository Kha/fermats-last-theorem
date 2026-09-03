import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing

set_option autoImplicit false

theorem Ideal.comap_map_adicCompletion_eq_of_isNoetherianRing
    {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S] (𝔞 : Ideal S) :
    (𝔞.map (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comap
        (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) = 𝔞 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing.solution
