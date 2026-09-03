import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.Converse
open LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hν : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (v : HeightOneSpectrum (𝓞 ℚ)) (_hχv : IsUnramifiedCharAt χA v) :
    (∀ 𝔓 ∈ primeFibre ℚ K v,
      LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
        LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar ν 𝔓)) ∧
    inducedLevelAt K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v = inducedLevelAt K ν v ∧
    (∀ (c : ℕ) (W : LocalGL3 v → ℂ),
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g : LocalGL3 v, W (g * k) = W g) →
      ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g : LocalGL3 v,
        (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) (g * k) =
          (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt.solution
