import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq

set_option autoImplicit false

open IsLocalRing RingTheory

theorem Module.Flat.of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsRegularLocalRing R] [IsRegularLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq.solution
