import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (cG : ENNReal)
    (hG : ∀ H : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] H →
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v)) =
          cG * ∫⁻ x : Fin 4 → L ⊗[K] v.adicCompletion K,
            (if h : IsUnit (!![x 0, x 1; x 2, x 3] :
                Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
              ENNReal.ofReal
                ((‖Algebra.norm (v.adicCompletion K) (!![x 0, x 1; x 2, x 3] :
                    Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => ν))
    (Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal)
    (hΦ : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] Φ) :
    (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
     ∫⁻ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v)) =
      cG * ∫⁻ q : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
        ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
          (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
              if h' : IsUnit (!![1 + q.1 * q.2, q.1; q.2, 1] :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                Φ (Matrix.GeneralLinearGroup.mk'' _ h * Matrix.GeneralLinearGroup.mk'' _ h')
              else 0
            else 0) *
            ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ ∂(ν.prod ν) ∂(ν.prod ν) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart.solution
