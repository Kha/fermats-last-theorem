import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_Algebra_PatchingDatum_exists_module_of_bijective_of_exists_presentation

theorem Algebra.PatchingDatum.exists_module_of_bijective_of_exists_presentation
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (ℓ : ℕ) {R : Type} [CommRing R] [Algebra 𝒪 R]
    {T : Type} [CommRing T] [Nontrivial T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Bijective φ)
    (hCI : ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module T M) (_ : Nontrivial M),
      (∀ (x : R) (m : M), φ x • m = x • m) ∧
      ∃ r : ℕ, Nonempty (Algebra.PatchingDatum 𝒪 ℓ r R M) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PatchingDatum_exists_module_of_bijective_of_exists_presentation.solution
