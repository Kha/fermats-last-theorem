import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.Finiteness.Cardinality
import P2M.Util
import P2M.Sol.S_IharaLemma_IdempotentSplitting_finite_cornerRing

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.finite_cornerRing {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    [Module.Finite 𝒪 B] : Module.Finite 𝒪 (S.CornerRing i) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_IdempotentSplitting_finite_cornerRing.solution
