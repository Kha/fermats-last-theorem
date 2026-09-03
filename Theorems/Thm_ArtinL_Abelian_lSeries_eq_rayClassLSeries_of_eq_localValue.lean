import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_NumberField_CompletedRayL
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_lSeries_eq_rayClassLSeries_of_eq_localValue

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply

universe u v

theorem ArtinL.Abelian.lSeries_eq_rayClassLSeries_of_eq_localValue
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (hχ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      χ (primeClass K 𝔣 v hv) = ArtinL.Abelian.localValue ψ v)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → ¬ ArtinL.Abelian.IsUnramifiedAt ψ v)
    {s : ℂ} (hs : 1 < s.re) :
    ArtinL.Abelian.LSeries ψ s = M4aTorus.rayClassLSeries K 𝔣 χ s := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_lSeries_eq_rayClassLSeries_of_eq_localValue.solution
