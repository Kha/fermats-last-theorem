import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import P2M.Util
import P2M.Sol.S_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

universe u v

theorem M4aHerbrand.finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
    (E : Type u) (F : Type v) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (α : E) (hpos : ∀ τ : E →+* ℝ, 0 < τ α)
    (x : HeightOneSpectrum (𝓞 E) → (AdeleRing (𝓞 E) E)ˣ)
    (hx : ∀ u : HeightOneSpectrum (𝓞 E), x u ∈ idelesTrivialOn (𝓞 E) E ({u}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hxu : ∀ u : HeightOneSpectrum (𝓞 E),
      ((finPart u (x u) : (u.adicCompletion E)ˣ) : u.adicCompletion E) = algebraMap E (u.adicCompletion E) α) :
    (Function.mulSupport fun u : HeightOneSpectrum (𝓞 E) => r (x u)).Finite ∧
      ∏ᶠ u : HeightOneSpectrum (𝓞 E), r (x u) = 1 := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive.solution
