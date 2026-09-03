import Mathlib
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ ArtinL.Abelian.conductor ψ ↔ ¬ ArtinL.Abelian.IsUnramifiedAt ψ v := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt.solution
