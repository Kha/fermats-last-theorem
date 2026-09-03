import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isArithGenuineCuspRealizable_twist_rpow_absNorm
attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell LanglandsTunnell.Converse

theorem AutomorphicForm.isArithGenuineCuspRealizable_twist_rpow_absNorm
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K))
    (hd₁ : 0 < d₁)
    (Φ : AutomorphicForm.HeckeEigensystem K ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable K
      (AutomorphicForm.productionPinsOf K
        (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet K c u d₁ d₂)
        (fun N => NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K)
        (fun v => NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers K) K v)
        (NumberField.AdelicBox.adelicBox K)) Φ)
    (s : ℝ) :
    AutomorphicForm.IsArithGenuineCuspRealizable K
      (AutomorphicForm.productionPinsOf K
        (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet K c u d₁ d₂)
        (fun N => NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K)
        (fun v => NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers K) K v)
        (NumberField.AdelicBox.adelicBox K))
      (Φ.twist (fun p : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm p.asIdeal : ℝ) ^ (-(s)) : ℝ) : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArithGenuineCuspRealizable_twist_rpow_absNorm.solution
