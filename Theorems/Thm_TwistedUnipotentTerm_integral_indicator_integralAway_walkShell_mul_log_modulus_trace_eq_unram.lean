import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem TwistedUnipotentTerm.integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∀ (h : ℕ → ℂ) (R : ℕ), (∀ r, R < r → h r = 0) →
      Integrable (fun x => {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (WithZero.log (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) x * ((Real.log (LanglandsTunnell.TateLocal.modulus (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) : ℝ) : ℝ) : ℂ)) ν ∧
      ∫ x, {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
            HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}.indicator
          (fun x => h (WithZero.log (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) x * ((Real.log (LanglandsTunnell.TateLocal.modulus (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) : ℝ) : ℝ) : ℂ) ∂ν =
      ((ν {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L),
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈ w'.1.adicCompletionIntegers L}).toReal : ℂ) *
        ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
        (-(h 0) / ((Ideal.absNorm v.asIdeal : ℂ) - 1) +
          ∑ r ∈ Finset.Icc 1 R, h r *
            ((Ideal.absNorm w.1.asIdeal : ℂ) ^ r - (Ideal.absNorm w.1.asIdeal : ℂ) ^ (r - 1)) *
            ((r : ℂ) - 1 / ((Ideal.absNorm v.asIdeal : ℂ) - 1) + 1 / ((Ideal.absNorm w.1.asIdeal : ℂ) - 1))) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_integral_indicator_integralAway_walkShell_mul_log_modulus_trace_eq_unram.solution
