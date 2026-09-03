import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
open scoped IsMulCommutative

universe u v

theorem ArtinL.Abelian.apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (𝔪' : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪')
    (N : ℕ)
    (hN : ∀ (β : 𝓞 K) (hβ : β ≠ 0) (𝔪 : Ideal (𝓞 K)) (hc : principalUnit K β hβ ∈ coprimeToModulus K 𝔪),
      (∀ τ : K →+* ℝ, 0 < τ (β : K)) → β - 1 ∈ v.asIdeal ^ N * 𝔪' →
        ψ (artinSymbol K L 𝔪 ⟨principalUnit K β hβ, hc⟩) = 1)

    (𝔣 : Ideal (𝓞 K)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L (Module.finrank K L) 𝔣)
    (r : (AdeleRing (𝓞 K) K)ˣ →* (L ≃ₐ[K] L))
    (hr₁ : principalIdeles (𝓞 K) K ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 K) K)ˣ, IsAdjuster K 𝔣 u 1 →
      r u = ∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob K L w ^ placeOrd K (projFin K u) w)

    (x : (AdeleRing (𝓞 K) K)ˣ) (hx1 : IsAdjuster K (v.asIdeal ^ N * 𝔪') x 1)
    (hxinf : infPart x = 1)
    (hxu : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w) = 1) :
    ψ (r x) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one.solution
