import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_Algebra_PatchingDatum_nonempty_patchingLevel_bot
import Theorems.Thm_Algebra_PatchingLevel_free_and_ker_eq_span
import Theorems.Thm_RingHom_bijective_of_surjective_of_smul_eq
import Theorems.Thm_Module_Free_of_surjective_of_smul_eq
import P2M.Util
namespace P2MW.S_Algebra_PatchingDatum_bijective_and_free_of_surjective

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (P : Algebra.PatchingDatum 𝒪 ℓ r R M)
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module T M]
    (RtoT : R →ₐ[𝒪] T) (hsurj : Function.Surjective RtoT)
    (hcompat : ∀ (x : R) (m : M), RtoT x • m = x • m) :
    Function.Bijective RtoT ∧ Module.Free R M ∧ Module.Free T M ∧
      Module.annihilator R M = ⊥ ∧
      ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
        Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by
  obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hℓ
  obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span
  have hbij := (RtoT : R →+* T).bijective_of_surjective_of_smul_eq hcompat hsurj
  exact ⟨hbij, hfree, Module.Free.of_surjective_of_smul_eq (RtoT : R →+* T) hcompat hsurj, hann, _,
    ⟨((Ideal.quotientEquivAlgOfEq 𝒪 hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective L.ψ_surjective)).trans (AlgEquiv.ofBijective RtoT hbij)⟩⟩
