import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (ΦL Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (u v : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L γ * x) = u x)
    (hv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L), v (globalPoints (𝓞 L) L γ * x) = v x)
    (hu₂ : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL)) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀) ∧
    (∫ x in Φ₀, u x * conj (v x) ∂adelicGLHaar (Fin 2) (𝓞 L) L =
      ∫ x in ΦL, u x * conj (v x) ∂adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    (∫ x in Φ₀, sigmaSectionActOn K L D σ u x * conj (sigmaSectionActOn K L D σ v x) ∂adelicGLHaar (Fin 2) (𝓞 L) L =
      ∫ x in ΦL, u x * conj (v x) ∂adelicGLHaar (Fin 2) (𝓞 L) L) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab.solution
