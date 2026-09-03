import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem AutomorphicForm.exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ Y : L ⊗[K] v.adicCompletion K → ℝ≥0∞, Measurable Y ∧ ∫⁻ y, Y y ∂ν ≠ ⊤ ∧
      ∀ y : L ⊗[K] v.adicCompletion K, ∃ η t : L ⊗[K] v.adicCompletion K, IsUnit η ∧
        Y y = (ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (η ^ 2)‖)⁻¹ ∧
        ∃ k ∈ AutomorphicForm.semiLocalIntegralSet K L v,
          (!![1, 0; y, 1] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            !![Ring.inverse η, 0; 0, η] * !![1, t; 0, 1] * (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet.solution
