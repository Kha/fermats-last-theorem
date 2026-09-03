import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import P2M.Util
import P2M.Sol.S_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.restrictNormalHom_idelicArtinMap_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (L : Type) [Field L] [NumberField L] [Algebra E L] [Algebra L F] [IsScalarTower E L F] [IsGalois E L]
    [IsMulCommutative (L ≃ₐ[E] L)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (𝔣L : Ideal (𝓞 E)) (hadmL : NumberField.NormIndex.IsAdmissibleModulusOfDegree E L (Module.finrank E L) 𝔣L)
    (rL : (AdeleRing (𝓞 E) E)ˣ →* (L ≃ₐ[E] L))
    (hrL₁ : principalIdeles (𝓞 E) E ≤ rL.ker)
    (hrL₂ : rL.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E L).idelicNorm.range)
    (hrL₃ : Function.Surjective rL)
    (hrL₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣L u 1 →
      rL u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E L v ^ placeOrd E (projFin E u) v)
    (x : (AdeleRing (𝓞 E) E)ˣ) :
    AlgEquiv.restrictNormalHom L (r x) = rL x := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq.solution
