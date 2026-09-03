import Mathlib
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_AdeleRing_relIndex_ideleBox_unitIdelesOutside
import Theorems.Thm_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
import P2M.Util
namespace P2MW.S_NumberField_AdeleRing_relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false

theorem solution
    {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p K).Nonempty)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ S) :
    (NumberField.AdeleRing.ideleBox (NumberField.RingOfIntegers K) K (↑S)
        (fun v => (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
        (fun w => (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range)).relIndex
      (NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers K) K (↑S))
      = p ^ (2 * (S.card + Fintype.card (NumberField.InfinitePlace K))) := by
  rw [NumberField.AdeleRing.relIndex_ideleBox_unitIdelesOutside]
  simp only [Subgroup.index_eq_card]
  exact NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
    hp hζ S hS
