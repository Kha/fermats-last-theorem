import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_LanglandsTunnell_C8Character
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_raySymbol_artinValue_span_eq_one_of_artinPairCore
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2 LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem LanglandsTunnell.P2.raySymbol_artinValue_span_eq_one_of_artinPairCore
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    [IsMulCommutative (L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L)]
    {ζ : ℂ} (hζ : ζ ^ 4 = -1)
    (𝔣 : Ideal (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)))
    (σ : L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L)
    (hσ : ∀ g : L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L, g ∈ Subgroup.zpowers σ)
    (D : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ArtinFieldCore (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣 i)
    (P : ∀ i j : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ArtinPairCore (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣 σ (D i) (D j))
    {𝔣₀ : Ideal (𝓞 ℚ)} (h0 : IsAdmissibleModulus ℚ L 𝔣₀)
    (hdiv : modulusExt ℚ (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣₀ ∣ 𝔣)
    (h𝔣 : 𝔣 ≠ ⊥)
    (hH1_i : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣),
      ((narrowRaySubgroup (D i).E (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪)).subgroupOf (coprimeToModulus (D i).E (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪)) ⊔
          ((coprimeToModulus (D i).N (((modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪)).map (algebraMap (𝓞 (D i).E) (𝓞 (D i).N)))).map
            (raySymbolUnitsHom (D i).N (fun w : HeightOneSpectrum (𝓞 (D i).N) =>
              primeUnit (D i).E (w.under (𝓞 (D i).E)) ^ ((w.under (𝓞 (D i).E)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
            (coprimeToModulus (D i).E (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪))).index ∣ Nat.card ((D i).N ≃ₐ[(D i).E] (D i).N))
    (hH1 :
      ((narrowRaySubgroup (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣).subgroupOf (coprimeToModulus (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣) ⊔
          ((coprimeToModulus L ((𝔣).map (algebraMap (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) (𝓞 L)))).map
            (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
              primeUnit (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (w.under (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) ^ ((w.under (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
            (coprimeToModulus (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣)).index ∣ Nat.card (L ≃ₐ[(FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)] L))
    (hdata_i : ∀ i : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ∀ F : IntermediateField (D i).E (D i).N,
      (Module.finrank (D i).E F).Prime →
      IdeleFirstIneqData (D i).E (D i).N F (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (D i).E (D i).𝔪))
    (hdata_ij : ∀ i j : ↥(primeCarriers (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) 𝔣), ∀ F : IntermediateField (P i j).E'' (P i j).N'',
      (Module.finrank (P i j).E'' F).Prime →
      IdeleFirstIneqData (P i j).E'' (P i j).N'' F (modulusExt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (P i j).E'' (P i j).𝔪''))
    (hdata : IdeleFirstIneqDataAt (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) L 𝔣)
    (α : 𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hαpos : ∀ τ : (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) →+* ℝ, 0 < τ (algebraMap (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) α)) :
    raySymbol (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (artinValue e hζ)
        ((Ideal.span {α} : Ideal (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) : FractionalIdeal ((𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))⁰) (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue_span_eq_one_of_artinPairCore.solution
