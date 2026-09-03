import Mathlib
import Definitions.Def_Patching_SystemTypes
import P2M.Util
import P2M.Sol.S_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes

open IsLocalRing RingTheory
theorem Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (Module.depth R M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by p2m_exact_reverting @_root_.P2MW.S_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes.solution
