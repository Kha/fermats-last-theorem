import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrableOn_norm_sq_mul_bruhatMajorant_mul_ideleNorm_rpow_inter_centreCutSiegelSet
attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.integrableOn_norm_sq_mul_bruhatMajorant_mul_ideleNorm_rpow_inter_centreCutSiegelSet
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (_hc : 0 < c) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (_h𝓕m : MeasurableSet 𝓕)
    (t : AdelicGL2 (𝓞 K) K) (w : ℝ) (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxc : Continuous x)
    (_hdecay : ∀ N : ℕ, IntegrableOn (fun g : AdelicGL2 (𝓞 K) K => ‖x g‖ * ‖x g‖ *
        (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 K) K))
    (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 K) K → ℂ) (_hφc : Continuous φ) (Cφ : ℝ)
    (_hCφ : ∀ g : AdelicGL2 (𝓞 K) K, ‖φ g‖ ≤ Cφ * adelicHeight K g ^ (s.re + 1 / 2))
    (_hsum : ∀ g : AdelicGL2 (𝓞 K) K, Summable (fun ξ : K =>
      ‖φ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖)) :
    IntegrableOn (fun g : AdelicGL2 (𝓞 K) K => ‖x g‖ ^ 2 * (‖φ g‖ + ∑' ξ : K, ‖φ (adelicWeyl (𝓞 K) K *
          unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 K) K) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrableOn_norm_sq_mul_bruhatMajorant_mul_ideleNorm_rpow_inter_centreCutSiegelSet.solution
