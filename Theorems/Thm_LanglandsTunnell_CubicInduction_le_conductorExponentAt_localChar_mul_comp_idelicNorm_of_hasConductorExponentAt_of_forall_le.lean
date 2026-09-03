import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_le_conductorExponentAt_localChar_mul_comp_idelicNorm_of_hasConductorExponentAt_of_forall_le
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.le_conductorExponentAt_localChar_mul_comp_idelicNorm_of_hasConductorExponentAt_of_forall_le
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (ξA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (B c₀ : ℕ)
    (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ξA p) B)
    (hν : ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar ν w) c)
    (hB : c₀ + 12 ≤ B) :
    ∀ w ∈ primeFibre ℚ K p,
      B ≤ LanglandsTunnell.TateLocal.conductorExponentAt K w
        (NumberField.TateGlobal.localChar (ν * ξA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_le_conductorExponentAt_localChar_mul_comp_idelicNorm_of_hasConductorExponentAt_of_forall_le.solution
