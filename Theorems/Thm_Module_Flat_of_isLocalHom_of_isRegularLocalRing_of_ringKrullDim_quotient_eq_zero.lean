import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open IsLocalRing

theorem Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hfib : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0)
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero.solution
