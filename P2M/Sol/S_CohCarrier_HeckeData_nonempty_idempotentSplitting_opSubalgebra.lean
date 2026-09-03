import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_IharaLemma_nonempty_idempotentSplitting_of_finite
import Mathlib.RingTheory.Noetherian.Basic
import P2M.Util
namespace P2MW.S_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra

set_option autoImplicit false

open scoped IsMulCommutative

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 V k) :
    Nonempty (IharaLemma.IdempotentSplitting ↥D.opSubalgebra) :=
  haveI : Module.Finite 𝒪 ↥D.opSubalgebra :=
    Module.Finite.of_injective D.opSubalgebra.val.toLinearMap fun _ _ h => Subtype.ext h
  IharaLemma.nonempty_idempotentSplitting_of_finite 𝒪 ↥D.opSubalgebra
