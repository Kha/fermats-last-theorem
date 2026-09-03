import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_Module_depth_quotient_eq_depth

open IsLocalRing RingTheory
theorem Module.depth_quotient_eq_depth
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    Module.depth (R ⧸ I) N = Module.depth R N := by p2m_exact_reverting @_root_.P2MW.S_Module_depth_quotient_eq_depth.solution
