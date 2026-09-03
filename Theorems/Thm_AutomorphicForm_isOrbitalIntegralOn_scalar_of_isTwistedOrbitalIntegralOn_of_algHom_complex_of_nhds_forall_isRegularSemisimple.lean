import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
    (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
    (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℂ σ ι hdeg hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
      HasCompactSupport φ)
    (f : GL (Fin 2) ℂ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport f)
    (c : ℂˣ)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ δ : GL (Fin 2) (L ⊗[K] ℂ), IsRegularSemisimple (normString K L ℂ σ δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (L ⊗[K] ℂ), IsNormConjugator K L ℂ σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
        (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
        Coupled K L ℂ σ γ δ y τ τ' →
        ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
          IsOrbitalIntegralOn ℂ μA γ τ f I → I' = I) :
    ∀ δ y : GL (Fin 2) (L ⊗[K] ℂ),
      IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ)))
            (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
        (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
        Coupled K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
        ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
          IsOrbitalIntegralOn ℂ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple.solution
