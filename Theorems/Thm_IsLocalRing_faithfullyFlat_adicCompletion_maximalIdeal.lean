import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
set_option autoImplicit false

theorem IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal.solution
