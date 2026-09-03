import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_IharaLemma_nonempty_idempotentSplitting_of_finite

set_option autoImplicit false

theorem IharaLemma.nonempty_idempotentSplitting_of_finite (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsNoetherianRing 𝒪] (B : Type) [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] :
    Nonempty (IharaLemma.IdempotentSplitting B) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_nonempty_idempotentSplitting_of_finite.solution
