import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrable_mul_apply_mul_conj_mul_ideleNorm_det_rpow_prod_restrict_of_memLp
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.integrable_mul_apply_mul_conj_mul_ideleNorm_det_rpow_prod_restrict_of_memLp
    (F : Type) [Field F] [NumberField F]
    [SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F)]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (_hd : d₁ < d₂)
    (_hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ → ℂ) (_hχ : ∀ n, χ n ≠ 0)
    (_hΦc : Continuous Φ)
    (_hmem : MemLp Φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (_hΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), Φ (globalPoints (𝓞 F) F γ * w) = Φ w)
    (_hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), Φ (centralScalar (𝓞 F) F n * w) = χ n * Φ w)
    (α β : ℝ) (_hα : 0 < α) (_hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F)) (_hSm : MeasurableSet S) (_hSs : S ⊆ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (_hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (_hfc : Continuous f) (_hfs : HasCompactSupport f)
    (Y : AdelicGL2 (𝓞 F) F → ℂ) (_hYc : Continuous Y)
    (_hY : MemLp Y 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) (w : ℝ) :
    Integrable (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        Φ (p.1 * p.2) * f p.2 * (starRingEnd ℂ) (Y p.1) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
    Integrable (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        Y p.1 * (starRingEnd ℂ) (Φ (p.1 * p.2) * f p.2) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrable_mul_apply_mul_conj_mul_ideleNorm_det_rpow_prod_restrict_of_memLp.solution
