import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
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
    (a b : v.adicCompletion K) (hab : a ≠ b)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0)
    (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hττ' : @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)) Subtype.val τ' =
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ)
        (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K))
        (fun s => AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (s : GL (Fin 2) (v.adicCompletion K))) τ)
    (β : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ)
    (hβm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ : ∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        (letI := AutomorphicForm.localCentralizerBorel K v γ
         ∫ t : AutomorphicForm.localCentralizer K v γ,
            β (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
              (t : GL (Fin 2) (v.adicCompletion K)) * u) ∂τ) = 1)
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] φ)
    (w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ)
    (hw : AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' φ w) :
    (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
     ∫⁻ x, ‖φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x)‖ₑ * ENNReal.ofReal (w x)
       ∂(AutomorphicForm.semiLocalHaar K L v)) =
      cG * ∫⁻ q : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
        ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
          (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
              if h' : IsUnit (!![1 + q.1 * q.2, q.1; q.2, 1] :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                ‖φ ((Matrix.GeneralLinearGroup.mk'' _ h * Matrix.GeneralLinearGroup.mk'' _ h')⁻¹ * δ *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ
                      (Matrix.GeneralLinearGroup.mk'' _ h * Matrix.GeneralLinearGroup.mk'' _ h'))‖ₑ *
                  ENNReal.ofReal (β (Matrix.GeneralLinearGroup.mk'' _ h))
              else 0
            else 0) *
            ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ ∂(ν.prod ν) ∂(ν.prod ν) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal.solution
