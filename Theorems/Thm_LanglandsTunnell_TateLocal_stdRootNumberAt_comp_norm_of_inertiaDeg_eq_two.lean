import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (hf : v.asIdeal.inertiaDeg' w.1.asIdeal = 2)
    (μ : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ) (ha : HasConductorExponentAt E v μ a)
    (hμ : ‖(μ (uniformizerUnit E v) : ℂ)‖ = 1) :
    HasConductorExponentAt M w.1
        (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) a ∧
      stdRootNumberAt M w.1
          (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) =
        (-1) ^ a * stdRootNumberAt E v μ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two.solution
