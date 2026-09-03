import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_NumberField_AdicCompletion_lintegral_inv_max_one_norm_sq_lt_top
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.AdicCompletion.lintegral_inv_max_one_norm_sq_lt_top
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    [MeasurableSpace (w.adicCompletion L)] [BorelSpace (w.adicCompletion L)]
    (ν : Measure (w.adicCompletion L)) [ν.IsAddHaarMeasure] :
    ∫⁻ y : w.adicCompletion L, (ENNReal.ofReal ((max 1 ‖y‖) ^ 2))⁻¹ ∂ν < ⊤ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdicCompletion_lintegral_inv_max_one_norm_sq_lt_top.solution
