import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm NumberField.TateGlobal
open M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.RankinSelberg.eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ) (hcμ : Continuous μ)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 ℚ) ℚ η) (hcη : Continuous η)
    (h : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
      IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
      ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
        ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
          (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) :
    μ = η.comp (genuineBaseChange ℚ K).idelicNorm := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg.solution
