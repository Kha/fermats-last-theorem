import Mathlib
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (ArtinL.Abelian.coeff ψ) s ∧ ArtinL.Abelian.LSeries ψ s ≠ 0 ∧
      HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
        (1 - ArtinL.Abelian.localValue ψ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
        (ArtinL.Abelian.LSeries ψ s) := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd.solution
