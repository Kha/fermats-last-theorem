import Definitions.Def_Patching_SystemTypes
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Support
import P2M.Util
import P2M.Sol.S_Module_depth_le_ringKrullDim

theorem Module.depth_le_ringKrullDim {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim R := by p2m_exact_reverting @_root_.P2MW.S_Module_depth_le_ringKrullDim.solution
