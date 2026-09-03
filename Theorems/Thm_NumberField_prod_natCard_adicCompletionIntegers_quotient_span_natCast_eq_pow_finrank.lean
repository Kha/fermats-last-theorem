import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false
theorem NumberField.prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank {K : Type*} [Field K]
    [NumberField K] {p : ℕ} (hp : p.Prime)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ S) :
    ∏ v ∈ S, Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(p : v.adicCompletionIntegers K)})
      = p ^ Module.finrank ℚ K := by p2m_exact_reverting @_root_.P2MW.S_NumberField_prod_natCard_adicCompletionIntegers_quotient_span_natCast_eq_pow_finrank.solution
