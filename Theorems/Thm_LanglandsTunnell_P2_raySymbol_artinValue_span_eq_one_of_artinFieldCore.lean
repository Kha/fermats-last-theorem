import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_LanglandsTunnell_C8Character
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_raySymbol_artinValue_span_eq_one_of_artinFieldCore

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2 LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem LanglandsTunnell.P2.raySymbol_artinValue_span_eq_one_of_artinFieldCore
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    [IsMulCommutative (L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L)]
    {ζ : ℂ} (hζ : ζ ^ 4 = -1)
    (𝔣 : Ideal (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)))
    (σ : L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L)
    (hσ : ∀ g : L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L, g ∈ Subgroup.zpowers σ)
    (D : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ArtinFieldCore (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣 i)
    (hI : ∀ v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)), ¬ v.asIdeal ∣ 𝔣 →
      (primeOver (c8H e) v).inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hcross : ∀ i j : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣),
      ∃ (b : (D i).Ip) (b' : (D j).Ip), (D i).Ni b = (D j).Ni b' ∧ (D i).ωpi b = σ)
    (hCSb_i : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣),
      SecondInequalityCTM (D i).E (D i).N (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪))
    (hFI_i : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ∀ F : IntermediateField (D i).E (D i).N,
      (Module.finrank (D i).E F).Prime → FirstInequalityCTM (D i).E F (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪))
    (hCSb : SecondInequalityCTM (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣) (hCSc1 : FirstInequalityCTM (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣)
    (α : 𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) (hα : α ≠ 0) (hα𝔣 : α - 1 ∈ 𝔣)
    (hαpos : ∀ τ : (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) →+* ℝ,
      0 < τ (algebraMap (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) α)) :
    raySymbol (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (artinValue e hζ)
      ((Ideal.span {α} : Ideal (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) : FractionalIdeal ((𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))⁰) (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue_span_eq_one_of_artinFieldCore.solution
