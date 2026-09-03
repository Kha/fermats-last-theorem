import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction
attribute [-instance] FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.cosetSum_adjoint_weightedPairing_of_isLsXiFunction
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (U : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hU : ∀ u ∈ U, NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1)
    (φ ψ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (hψ : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ ψ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ₂ : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hψ₂ : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hφU : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g)
    (hψU : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, ∀ u ∈ U, ψ (g * u) = ψ g)
    (gv : AutomorphicForm.AdelicGL2 (𝓞 K) K) (n : ℕ) (reps : Fin n → AutomorphicForm.AdelicGL2 (𝓞 K) K)
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * gv * u')
    (c : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))
    (hc : ∃ u ∈ U, ∃ u' ∈ U,
      gv⁻¹ = AutomorphicForm.centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u * gv * u')) :
    MemLp (fun x => ∑ i, φ (x * reps i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (fun x => ∑ i, ψ (x * reps i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    ∫ x in Φ₀, (∑ i, φ (x * reps i)) * conj (ψ x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) *
        conj ((ξ c : ℂˣ) : ℂ) *
        ∫ x in Φ₀, φ x * conj (∑ i, ψ (x * reps i)) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction.solution
