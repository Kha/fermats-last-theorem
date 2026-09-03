import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hfin : Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ∃ (ν : @Measure (AdelicGL2 (𝓞 F) F) (glBorel (Fin 2) (𝓞 F) F)) (M : ℝ≥0∞)
      (χ : AdelicGL2 (𝓞 F) F → ℝ≥0∞),
      M ≠ ⊤ ∧ (∀ x, χ x ≠ 0 ∧ χ x ≠ ⊤) ∧
      (∀ k ∈ finiteAdelicGL2Subgroup F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F → χ k = 1) ∧
      ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
        @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ≤
            M * @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
              ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
                (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
              (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ∧
        @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
              ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
                (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
              (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ≤
            M * @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ∧
        ∀ x : AdelicGL2 (𝓞 F) F,
          @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2) =
            χ x * @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.solution
