import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K)) (l : (v.adicCompletion K)ˣ)
    (hl : ∀ x : L ⊗[K] v.adicCompletion K,
      x * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x ≠
        algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (l : v.adicCompletion K))
    (g : GL (Fin 2) (v.adicCompletion K))
    (hg : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; (l : v.adicCompletion K), 0])
    (β : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hβ : β = AutomorphicForm.toTensorGL K L (v.adicCompletion K) g) :
    ∃ W : Set (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ β),
      IsOpen W ∧ (1 : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ β) ∈ W ∧
      ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, AutomorphicForm.IsSemiLocalTestFn K L v φv →
        tsupport φv ⊆
          {δ' | ∃ t ∈ W,
            AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
              ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * β) δ'} →
        ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, AutomorphicForm.IsLocalTestFn K v fv ∧
          (∀ t ∈ W, ∀ δ₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              δ₁ = (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * β →
            AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₁) →
            ∀ γ : GL (Fin 2) (v.adicCompletion K), AutomorphicForm.IsRegularSemisimple γ →
            ∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ₁ y →
            ∀ (τ : @MeasureTheory.Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
                (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
              (τ' : @MeasureTheory.Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₁)
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁)),
              @MeasureTheory.Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ →
              @MeasureTheory.Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁) τ' →
              AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ δ₁ y τ τ' →
              ∀ I I' : ℂ,
                AutomorphicForm.IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ
                  (AutomorphicForm.semiLocalHaar K L v) δ₁ τ' φv I' →
                AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ fv I →
                I' = I) ∧
          ∀ γ : GL (Fin 2) (v.adicCompletion K), AutomorphicForm.IsRegularSemisimple γ →
            (¬ ∃ δ ∈ tsupport φv, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ δ) →
            ∀ τ : @MeasureTheory.Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
              (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ),
              @MeasureTheory.Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ →
              ∀ I : ℂ,
                AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ fv I →
                I = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne.solution
