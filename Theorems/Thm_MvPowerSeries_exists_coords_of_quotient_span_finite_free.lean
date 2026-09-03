import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Defs
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_coords_of_quotient_span_finite_free

universe u
theorem MvPowerSeries.exists_coords_of_quotient_span_finite_free
    {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {r : ℕ} (f : Fin r → MvPowerSeries (Fin r) 𝒪)
    [Module.Finite 𝒪 (MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f))]
    [Module.Free 𝒪 (MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f))]
    (φ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] MvPowerSeries (Fin r) 𝒪) (hφ : ∀ i, φ (MvPowerSeries.X i) = f i) :
    ∃ (e : ℕ) (β : Fin e → MvPowerSeries (Fin r) 𝒪),
      (∀ x : MvPowerSeries (Fin r) 𝒪, ∃ c : Fin e → MvPowerSeries (Fin r) 𝒪, x = ∑ j, φ (c j) * β j) ∧
      (∀ c : Fin e → MvPowerSeries (Fin r) 𝒪, ∑ j, φ (c j) * β j = 0 → ∀ j, c j = 0) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_coords_of_quotient_span_finite_free.solution
