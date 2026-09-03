import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (Ψ : GL (Fin 2) A × GL (Fin 2) A ≃* GL (Fin 2) (L ⊗[K] A))
    (hΨc : Continuous Ψ) (hΨc' : Continuous Ψ.symm)
    (hΨ₁ : ∀ g : GL (Fin 2) A, Ψ (g, g) = toTensorGL K L A g)
    (hΨσ : ∀ p : GL (Fin 2) A × GL (Fin 2) A, sigmaGL K L A σ (Ψ p) = Ψ p.swap)
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
    μA.IsHaarMeasure → μL = Measure.map Ψ (μA.prod μA) →
    (∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → HasCompactSupport φ →
      (Continuous fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) ∧
      (HasCompactSupport fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA)) ∧
    ∀ γ : GL (Fin 2) A, IsRegularSemisimple γ →
    ∀ δ : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ 1 →
    ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
      (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
      Coupled K L A σ γ δ 1 τ τ' →
    ∀ C : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact C →
    ∀ w : GL (Fin 2) A → ℝ, Continuous w → HasCompactSupport w → (∀ x, 0 ≤ w x) →
      (∀ x : GL (Fin 2) A, (∃ h : GL (Fin 2) A, Ψ (h, h⁻¹ * (x⁻¹ * γ * x)) ∈ C) →
        ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), w (t * x) ∂τ = 1) →
    ∃ w' : GL (Fin 2) (L ⊗[K] A) → ℝ, Continuous w' ∧ HasCompactSupport w' ∧ (∀ x, 0 ≤ w' x) ∧
      ∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → tsupport φ ⊆ C →
        IsSectionFnOn A γ τ (fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) w ∧
        IsTwistedSectionFnOn K L A σ δ τ' φ w' ∧
        ∫ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) * (w' x : ℂ) ∂μL =
          ∫ x, (fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) (x⁻¹ * γ * x) * (w x : ℂ) ∂μA := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod.solution
