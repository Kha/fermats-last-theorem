import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  M4aHerbrand.GenuineDescent

theorem NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) :
    localChar (ξ * μ.comp (genuineBaseChange E M).idelicNorm) w.1 =
      localChar ξ w.1 * (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange.solution
