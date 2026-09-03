import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import P2M.Util
import P2M.Sol.S_Algebra_PatchingDatum_bijective_and_exists_presentation_of_surjective_of_exists

theorem Algebra.PatchingDatum.bijective_and_exists_presentation_of_surjective_of_exists
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {T : Type} [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ)
    (hTW : ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module T M)
      (_ : Nontrivial M),
      (∀ (x : R) (m : M), φ x • m = x • m) ∧
      ∃ r : ℕ, Nonempty (Algebra.PatchingDatum 𝒪 ℓ r R M)) :
    Function.Bijective φ ∧
    (∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module T M)
      (_ : Nontrivial M),
      (∀ (x : R) (m : M), φ x • m = x • m) ∧
      Module.Free R M ∧ Module.Free T M ∧ Module.annihilator R M = ⊥) ∧
    ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PatchingDatum_bijective_and_exists_presentation_of_surjective_of_exists.solution
