import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Defs
import P2M.Util
import P2M.Sol.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free

universe u
theorem Algebra.PatchingDatum.nonempty_of_exists_presentation_of_free
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (ℓ : ℕ) {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R] [Module.Free 𝒪 R]
    (hCI : ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
      Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] R))
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Nonempty (Algebra.PatchingDatum 𝒪 ℓ r R M) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free.solution
