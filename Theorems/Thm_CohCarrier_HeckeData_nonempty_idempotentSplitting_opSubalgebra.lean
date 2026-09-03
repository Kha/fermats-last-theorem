import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra

open scoped IsMulCommutative

theorem CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 V k) :
    Nonempty (IharaLemma.IdempotentSplitting ↥D.opSubalgebra) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra.solution
