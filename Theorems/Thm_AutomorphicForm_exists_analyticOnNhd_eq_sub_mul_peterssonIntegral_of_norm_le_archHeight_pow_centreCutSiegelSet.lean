import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F]
    (w a c u d₁ d₂ : ℝ) (_hc : 0 < c) (ι : Type) [Fintype ι] (t : ι → AdelicGL2 (𝓞 F) F)
    (𝓕 : Set (AdelicGL2 (𝓞 F) F)) (_h𝓕m : MeasurableSet 𝓕)
    (_h𝓕cov : 𝓕 ⊆ ⋃ i, (· * t i) '' centreCutSiegelSet F c u d₁ d₂)
    (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hGan : ∀ g, AnalyticOnNhd ℂ (fun s => G s g) {s : ℂ | a < s.re})
    (_hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (_hGbd : ∀ (C : Set ℂ), IsCompact C → C ⊆ {s : ℂ | a < s.re} → ∀ i : ι,
      ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ centreCutSiegelSet F c u d₁ d₂,
        ‖G s (g * t i)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)
    (x y : AdelicGL2 (𝓞 F) F → ℂ) (_hxc : Continuous x) (_hyc : Continuous y)
    (_hdecay : ∀ (i : ι) (N : ℕ), IntegrableOn
      (fun g => ‖x g‖ * ‖y g‖ * (1 + archHeight F (glArch (𝓞 F) F (g * (t i)⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t i) '' centreCutSiegelSet F c u d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) {s : ℂ | a < s.re} ∧
    ∀ (s₀ : ℂ) (σ₁ : ℝ) (E : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), σ₁ < s.re → G s g = (s - s₀) * E s g) →
      ∀ s : ℂ, σ₁ < s.re → a < s.re →
        (∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
        (s - s₀) * peterssonIntegral F w 𝓕 (fun g => x g * E s g) y := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet.solution
