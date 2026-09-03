import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.FreeModule.Basic
import P2M.Util
import P2M.Sol.S_IharaLemma_IdempotentSplitting_free_cornerRing

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.free_cornerRing {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    [IsLocalRing 𝒪] [Module.Finite 𝒪 B] [Module.Free 𝒪 B] :
    Module.Free 𝒪 (S.CornerRing i) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_IdempotentSplitting_free_cornerRing.solution
