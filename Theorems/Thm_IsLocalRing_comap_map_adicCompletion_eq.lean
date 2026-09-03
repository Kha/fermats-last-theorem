import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_comap_map_adicCompletion_eq

theorem IsLocalRing.comap_map_adicCompletion_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = I := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_comap_map_adicCompletion_eq.solution
