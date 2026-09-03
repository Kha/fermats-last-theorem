import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem
AutomorphicForm.exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : ¬ AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀))
    (c : (v.adicCompletion K)ˣ)
    (hc : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀) :
    ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, AutomorphicForm.IsSemiLocalTestFn K L v φv →
      ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, AutomorphicForm.IsLocalTestFn K v fv ∧
        (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
            AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ) →
            ∀ γ ∈ V, AutomorphicForm.IsRegularSemisimple γ →
            ∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
              (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
              AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ δ y τ τ' →
              ∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I' →
                AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I' = I) ∧
          (∀ γ ∈ V, AutomorphicForm.IsRegularSemisimple γ →
            (¬ ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ δ) →
            ∀ τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I = 0)) ∧
        (∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀ y →
          ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
              (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₀)
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₀)),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₀) τ' →
            AutomorphicForm.Coupled K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀ y τ τ' →
            ∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ₀ τ' φv I' →
              AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ fv I →
                I' = I) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.solution
