import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.RankinSelberg.exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
    (K : Type) [Field K] [NumberField K]
    (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w₀ w₂ : p₀.Extension (𝓞 K)) (hne : w₀.1 ≠ w₂.1) :
    ∃ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 ∧
      (∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 ℚ) ≠ p₀ →
        ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1) ∧
      (∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1) ∧
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w₀.1 ≠ 1 ∧
      (genuineBaseChange ℚ K).idelicNorm u = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne.solution
