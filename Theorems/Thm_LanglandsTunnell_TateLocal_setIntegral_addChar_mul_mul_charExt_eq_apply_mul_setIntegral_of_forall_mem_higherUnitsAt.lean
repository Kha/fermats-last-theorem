import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem
  LanglandsTunnell.TateLocal.setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a h : ℕ) (hh : 1 ≤ h) (hah : a ≤ 2 * h)
    (hχa : ∀ u ∈ higherUnitsAt K v a, χ u = 1)
    (c : v.adicCompletion K)
    (hc : ∀ u ∈ higherUnitsAt K v h, ((χ u : ℂˣ) : ℂ) = ψ (c * ((u : v.adicCompletion K) - 1)))
    (z : v.adicCompletion K) (hz : Valued.v z = WithZero.exp (n + a))
    (f : v.adicCompletion K → ℂ)
    (hf : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ w ∈ higherUnitsAt K v (a - h), f ((u : v.adicCompletion K) * w) = f u) :
    (∀ u₁ : v.adicCompletion K, Valued.v u₁ = 1 → Valued.v (z * u₁ + c) ≤ WithZero.exp (n + h) →
      (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * f u * charExt χ u ∂μ) =
        f u₁ * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * charExt χ u ∂μ) ∧
    ((∀ u : v.adicCompletion K, Valued.v u = 1 → WithZero.exp (n + h) < Valued.v (z * u + c)) →
      (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (z * u) * f u * charExt χ u ∂μ) = 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_mul_charExt_eq_apply_mul_setIntegral_of_forall_mem_higherUnitsAt.solution
