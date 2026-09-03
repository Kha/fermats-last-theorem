import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_depth_self_eq_ringKrullDim

set_option autoImplicit false

open IsLocalRing RingTheory

theorem IsRegularLocalRing.depth_self_eq_ringKrullDim
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsRegularLocalRing R] :
    (Module.depth R R : WithBot ℕ∞) = ringKrullDim R := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_depth_self_eq_ringKrullDim.solution
