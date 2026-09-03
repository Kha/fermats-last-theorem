import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (c : ℂˣ)
    (δ y : GL (Fin 2) (L ⊗[K] ℂ))
    (hδ : IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ)))
        (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) := borel _
       letI := centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel K L ℂ σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℂ =>
               Y.map (fun x : ℂ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℂ))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) * X.map (sigmaTensor K L ℂ σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer
               ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ))) =>
             ((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map
               (fun x : ℂ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℂ))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] ℂ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L ℂ σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] ℂ)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] ℂ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    ∃ y' : GL (Fin 2) (L ⊗[K] ℂ),
      IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
      Coupled K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex.solution
