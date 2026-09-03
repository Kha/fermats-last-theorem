import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain LanglandsTunnell.Converse
  M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (w' : InfinitePlace M) (u : ℂ) :
    (∀ (_ : w'.IsReal) (a : ℤ), IsArchCompAt E μ (w'.comap (algebraMap E M)) u a →
        IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u a) ∧
    (∀ (_ : w'.IsComplex) (_ : (w'.comap (algebraMap E M)).IsReal) (a : ℤ),
        IsArchCompAt E μ (w'.comap (algebraMap E M)) u a →
        IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u 0) ∧
    (∀ (_ : w'.IsComplex) (_ : (w'.comap (algebraMap E M)).IsComplex) (k : ℤ),
        IsArchCompAt E μ (w'.comap (algebraMap E M)) u k →
        IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u k ∨
          IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u (-k)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange.solution
