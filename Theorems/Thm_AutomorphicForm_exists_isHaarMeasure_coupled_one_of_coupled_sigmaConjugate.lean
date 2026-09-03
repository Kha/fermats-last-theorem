import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμ : ∀ g : GL (Fin 2) (L ⊗[K] A),
      @Measure.map _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A))
        (fun z => g * z) μ = μ)
    (γ : GL (Fin 2) A) (δ x : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (hC : AutomorphicForm.Coupled K L A σ γ δ x τ τ') :
    ∃ τ₁ : @Measure (AutomorphicForm.twistedCentralizer K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x))
        (AutomorphicForm.twistedCentralizerBorel K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x)),
      @Measure.IsHaarMeasure _ _ _
          (AutomorphicForm.twistedCentralizerBorel K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x)) τ₁ ∧
        AutomorphicForm.Coupled K L A σ γ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) 1 τ τ₁ ∧
        ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ),
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) τ₁
              φ I →
            AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.solution
