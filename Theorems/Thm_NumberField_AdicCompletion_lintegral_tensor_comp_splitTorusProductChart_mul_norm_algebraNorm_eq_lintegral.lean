import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_NumberField_AdicCompletion_lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.AdicCompletion.lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (H : (Fin 4 → L ⊗[K] v.adicCompletion K) → ENNReal) (hH : Measurable H) :
    ∫⁻ q, H ![q 0 + q 0 * q 1 * q 2, q 0 * q 1, q 3 * q 2, q 3] *
        ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (q 0 * q 3)‖
          ∂(Measure.pi fun _ : Fin 4 => ν) =
      ∫⁻ x, H x ∂(Measure.pi fun _ : Fin 4 => ν) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdicCompletion_lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral.solution
