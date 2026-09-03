import Mathlib
import P2M.Util
import P2M.Sol.S_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk

set_option autoImplicit false

open scoped TensorProduct

theorem LocalizedModule.exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk
    {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {M : Type} [AddCommGroup M] [Module 𝒪 M] [Module.Free 𝒪 M] [Module.Finite 𝒪 M]
    {T : Type} [AddCommGroup T] [Module B T] [Module.Finite B T]
    (x : PrimeSpectrum B) (r₀ : B) (hr₀ : r₀ ∉ x.asIdeal)
    (u : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal →
      (Localization.AtPrime y.asIdeal ⊗[𝒪] M →ₗ[Localization.AtPrime y.asIdeal]
        LocalizedModule y.asIdeal.primeCompl T))
    (hcont : ∀ v : M, ∃ (f : B) (t : T), f ∉ x.asIdeal ∧
      ∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal) (hf : f ∉ y.asIdeal),
        u y hy ((1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v) = LocalizedModule.mk t ⟨f, hf⟩)
    (hsurj : Function.Surjective (u x hr₀)) :
    ∃ r : B, r ∉ x.asIdeal ∧ r₀ ∣ r ∧ ∃ A : B ⊗[𝒪] M →ₗ[B] T,
      (∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), r ∉ y.asIdeal → ∀ v : M,
        LocalizedModule.mk (A ((1 : B) ⊗ₜ[𝒪] v)) 1 =
          algebraMap B (Localization.AtPrime y.asIdeal) r •
            u y hy ((1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v)) ∧
      (∀ t : T, ∃ (w : B ⊗[𝒪] M) (n : ℕ), A w = r ^ n • t) := by p2m_exact_reverting @_root_.P2MW.S_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk.solution
