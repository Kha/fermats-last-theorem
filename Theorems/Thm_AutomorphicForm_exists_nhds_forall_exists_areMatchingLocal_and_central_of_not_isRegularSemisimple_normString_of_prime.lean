import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : ¬ AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀)) :
    ∃ U ∈ nhds δ₀, ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv → tsupport φv ⊆ U →
        ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ,
          AutomorphicForm.IsLocalTestFn K v fv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv fv ∧
          ∀ (c₁ : (v.adicCompletion K)ˣ) (δ₁ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
            AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
              (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) δ₁ y →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁))
                (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁)))
              (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₁)
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁)),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁)) τ →
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁) τ' →
              AutomorphicForm.Coupled K L (v.adicCompletion K) σ
                (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) δ₁ y τ τ' →
              (∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ₁ τ' φv I' →
                AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) τ fv I →
                  I' = I) ∧
              ((¬ ∃ δ ∈ tsupport φv, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) δ) →
                ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) τ fv I →
                  I = 0) ∧
              (∀ w' : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
                AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ₁ τ' φv w' →
                Integrable
                  (fun x => φv (x⁻¹ * δ₁ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) * (w' x : ℂ))
                  (AutomorphicForm.semiLocalHaar K L v)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime.solution
