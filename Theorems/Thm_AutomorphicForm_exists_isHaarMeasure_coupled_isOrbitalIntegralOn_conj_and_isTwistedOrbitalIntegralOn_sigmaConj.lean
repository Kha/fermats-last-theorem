import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isHaarMeasure_coupled_isOrbitalIntegralOn_conj_and_isTwistedOrbitalIntegralOn_sigmaConj

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.exists_isHaarMeasure_coupled_isOrbitalIntegralOn_conj_and_isTwistedOrbitalIntegralOn_sigmaConj
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) :
    (∀ (μA : @Measure (GL (Fin 2) A) (glBorelOf A)),
      (∀ g : GL (Fin 2) A, @Measure.map _ _ (glBorelOf A) (glBorelOf A) (fun z => g * z) μA = μA) →
      ∀ (γ x : GL (Fin 2) A)
        (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ →
        ∀ γ' : GL (Fin 2) A, γ' = x⁻¹ * γ * x →
          ∃ τ₀ : @Measure (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A))) (centralizerBorel A γ'),
            @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ') τ₀ ∧
            (∀ (δ y : GL (Fin 2) (L ⊗[K] A))
              (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
              Coupled K L A σ γ δ y τ τ' → Coupled K L A σ γ' δ (y * toTensorGL K L A x) τ₀ τ') ∧
            (∀ δ y : GL (Fin 2) (L ⊗[K] A),
              IsNormConjugator K L A σ γ δ y → IsNormConjugator K L A σ γ' δ (y * toTensorGL K L A x)) ∧
            ∀ (f : GL (Fin 2) A → ℂ) (I : ℂ),
              IsOrbitalIntegralOn A μA γ τ f I → IsOrbitalIntegralOn A μA γ' τ₀ f I) ∧
    (∀ (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))),
      (∀ g : GL (Fin 2) (L ⊗[K] A),
        @Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)) (fun z => g * z) μ = μ) →
      ∀ (γ : GL (Fin 2) A) (δ x : GL (Fin 2) (L ⊗[K] A))
        (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
        (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ' →
        Coupled K L A σ γ δ x τ τ' →
        ∀ δ' : GL (Fin 2) (L ⊗[K] A), δ' = x⁻¹ * δ * sigmaGL K L A σ x →
          ∃ τ₁ : @Measure (twistedCentralizer K L A σ δ') (twistedCentralizerBorel K L A σ δ'),
            @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ') τ₁ ∧
            Coupled K L A σ γ δ' 1 τ τ₁ ∧
            ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ),
              IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I →
                IsTwistedOrbitalIntegralOn K L A σ μ δ' τ₁ φ I) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_isOrbitalIntegralOn_conj_and_isTwistedOrbitalIntegralOn_sigmaConj.solution
