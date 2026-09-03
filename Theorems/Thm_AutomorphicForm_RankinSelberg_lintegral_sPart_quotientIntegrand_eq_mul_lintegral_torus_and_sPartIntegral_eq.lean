import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_RankinSelberg_lintegral_sPart_quotientIntegrand_eq_mul_lintegral_torus_and_sPartIntegral_eq
attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff
attribute [-simp] RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.RankinSelberg.lintegral_sPart_quotientIntegrand_eq_mul_lintegral_torus_and_sPartIntegral_eq
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c : ℝ≥0∞)
      (_hc : ∀ (D : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
        ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
          (∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
          ∫⁻ q, f q.out ∂(rationalCentreUnipotentQuotientMeasure K) =
            c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
                  f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
                ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hD : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (e₁ e₂ : ℝ) (_he₁ : 0 < e₁) (_he : e₁ < e₂)
      (C : ℝ≥0∞) (_hC : ∀ r : ℝ, 0 < r →
        (NumberField.Idele.idelicHaar K) (D ∩ {z | NumberField.TateGlobal.ideleNorm K z ^ 2 * r ∈ Set.Icc e₁ e₂}) = C)
      (D₀ : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
      (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
      (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (_hψ : IsGlobalAddChar K ψ)
      (μ ν ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hZ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))
      (x y : AdelicGL2 (𝓞 K) K → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ) (_hφc : Continuous φ),
    (∫⁻ q in {q : RationalCentreUnipotentQuotient K | q.out ∈ RankinSelberg.shellZeroOutside K S},
        ‖RankinSelberg.quotientIntegrand K (productionPinsOf K D₀ U gen (adelicBox K)) ψ x y φ w e₁ e₂ q.out‖ₑ
        ∂(rationalCentreUnipotentQuotientMeasure K) =
      c * C * ∫⁻ t, ∫⁻ k,
          ‖whittakerCoefficient K (productionPinsOf K D₀ U gen (adelicBox K)) ψ x 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ U gen (adelicBox K)) ψ y 1
                (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
              φ (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖ₑ *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) ∧
    ((∫⁻ t, ∫⁻ k,
          ‖whittakerCoefficient K (productionPinsOf K D₀ U gen (adelicBox K)) ψ x 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ U gen (adelicBox K)) ψ y 1
                (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
              φ (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖ₑ *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) < ∞ →
      RankinSelberg.sPartIntegral K S (productionPinsOf K D₀ U gen (adelicBox K)) ψ x y φ w e₁ e₂ =
        (c.toReal : ℂ) * (C.toReal : ℂ) * ∫ t, ∫ k,
            whittakerCoefficient K (productionPinsOf K D₀ U gen (adelicBox K)) ψ x 1 (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ U gen (adelicBox K)) ψ y 1
                  (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
                φ (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ)
            ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_RankinSelberg_lintegral_sPart_quotientIntegrand_eq_mul_lintegral_torus_and_sPartIntegral_eq.solution
