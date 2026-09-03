import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (Φ Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AdelicGL2 (𝓞 L) L → E)
    (hF : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L),
      F (globalPoints (𝓞 L) L γ * x) = F x)
    (G : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L → E)
    (hG₁ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x y : AdelicGL2 (𝓞 L) L),
      G (globalPoints (𝓞 L) L γ * x) y = G x y)
    (hG₂ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x y : AdelicGL2 (𝓞 L) L),
      G x (globalPoints (𝓞 L) L γ * y) = G x y) :
    (IntegrableOn F Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ↔ IntegrableOn F Φ (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
    (∫ x in Φ₀, F x ∂adelicGLHaar (Fin 2) (𝓞 L) L = ∫ x in Φ, F x ∂adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    IsFundamentalDomain (globalPoints (𝓞 L) L).range (AutomorphicForm.sigmaAdelicAct K L D σ '' Φ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) ∧
    (IntegrableOn (fun x => G x (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) Φ₀
        (adelicGLHaar (Fin 2) (𝓞 L) L) ↔
      IntegrableOn (fun x => G (AutomorphicForm.sigmaAdelicAct K L D σ x) x) Φ
        (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
    (∫ x in Φ₀, G x (AutomorphicForm.sigmaAdelicAct K L D σ.symm x) ∂adelicGLHaar (Fin 2) (𝓞 L) L =
      ∫ x in Φ, G (AutomorphicForm.sigmaAdelicAct K L D σ x) x ∂adelicGLHaar (Fin 2) (𝓞 L) L) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab.solution
