import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
    LanglandsTunnell.CubicInduction.exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
      (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
      (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) ∧
      (Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1)) ∧
      (∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}))) ∧
      (∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁)) ∧
      (
          ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      g ∈ P ↔ (fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
        (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)
      ) ∧
      (∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
          ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (s x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      ∃ (μP : Measure ↥P) (c₀ : ℝ≥0∞),
        μP.IsMulRightInvariant ∧ μP.IsOpenPosMeasure ∧ IsFiniteMeasureOnCompacts μP ∧ c₀ ≠ 0 ∧ c₀ ≠ ⊤ ∧
          ν = c₀ •
      (Measure.map Quotient.mk''
        (μP.withDensity fun p : ↥P =>
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
              (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
            {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
                ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
                  k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
                    componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k}.indicator (fun _ => (1 : ℝ≥0∞))
              (p : AdelicGL 3 (𝓞 ℚ) ℚ)) :
        Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar.solution
