import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_Module_depth_eq_depth_of_finite_of_isLocalHom

open IsLocalRing RingTheory
theorem Module.depth_eq_depth_of_finite_of_isLocalHom
    (R : Type*) (S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] :
    Module.depth R M = Module.depth S M := by p2m_exact_reverting @_root_.P2MW.S_Module_depth_eq_depth_of_finite_of_isLocalHom.solution
