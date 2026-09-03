import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.FreeModule.Basic
import P2M.Util
import P2M.Sol.S_IharaLemma_free_cornerSubmodule

set_option autoImplicit false

theorem IharaLemma.free_cornerSubmodule {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
    (e : B) (he : IsIdempotentElem e) [IsLocalRing 𝒪] [Module.Finite 𝒪 V] [Module.Free 𝒪 V] :
    Module.Free 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_free_cornerSubmodule.solution
