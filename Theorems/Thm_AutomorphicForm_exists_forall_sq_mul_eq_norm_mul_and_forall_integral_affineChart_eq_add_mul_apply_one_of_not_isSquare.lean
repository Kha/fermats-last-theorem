import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure] :
    ∃ α : v.adicCompletion K → ℂ,
      (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t s : v.adicCompletion K, ‖t‖ < ε₀ → ¬ IsSquare t → s ≠ 0 → ‖s‖ ≤ 1 →
          α (s ^ 2 * t) = (‖s‖ : ℂ) * α t) ∧
      ∀ δ B : ℝ, 0 < δ →
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion K, ‖t‖ < ε → ¬ IsSquare t →
          α t ≠ 0 ∧
          ∀ Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ,
            (∀ M E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, ‖E i j‖ ≤ δ) → Φ (M + E) = Φ M) →
            (∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Φ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B) →
            ∀ J : v.adicCompletion K → ℂ,
              (∀ s : v.adicCompletion K, J s = ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
                Φ (1 + !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
                  (s - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(ν.prod μ)) →
              J t = J 0 + α t * Φ 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare.solution
