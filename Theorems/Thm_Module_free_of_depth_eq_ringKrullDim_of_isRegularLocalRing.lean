import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing

open IsLocalRing RingTheory
theorem Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (H : (Module.depth R M : WithBot ℕ∞) = ringKrullDim R) : Module.Free R M := by p2m_exact_reverting @_root_.P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.solution
