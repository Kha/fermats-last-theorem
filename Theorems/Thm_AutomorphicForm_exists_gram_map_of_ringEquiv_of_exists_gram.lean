import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_gram_map_of_ringEquiv_of_exists_gram

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_gram_map_of_ringEquiv_of_exists_gram
    {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
    [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
    [Algebra ℝ (L ⊗[K] A)] [Algebra ℝ (L' ⊗[K'] A')]
    (e : A ≃+* A') (he : Continuous e) (he' : Continuous e.symm)
    (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))
    (hEι : ∀ x : A, E ((1 : L) ⊗ₜ[K] x) = (1 : L') ⊗ₜ[K'] e x)
    (hEr : ∀ (r : ℝ) (z : L ⊗[K] A), E (r • z) = r • E z)
    (γ : GL (Fin 2) A) (γ' : GL (Fin 2) A') (hγ' : Matrix.GeneralLinearGroup.map e.toRingHom γ = γ')
    (δ : GL (Fin 2) (L ⊗[K] A)) (δ' : GL (Fin 2) (L' ⊗[K'] A'))
    (hδ' : Matrix.GeneralLinearGroup.map E.toRingHom δ = δ')
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ₀ : @Measure (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A'))) (centralizerBorel A' γ'))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (τ₀' : @Measure (twistedCentralizer K' L' A' σ' δ') (twistedCentralizerBorel K' L' A' σ' δ'))
    (hτ₀ : letI := glBorelOf A'; letI := centralizerBorel A γ; letI := centralizerBorel A' γ'
      Measure.map (fun t : Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
          Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ)
    (hτ₀' : letI := glBorelOf (L' ⊗[K'] A'); letI := twistedCentralizerBorel K L A σ δ;
      letI := twistedCentralizerBorel K' L' A' σ' δ'
      Measure.map (fun t : twistedCentralizer K' L' A' σ' δ' => (t : GL (Fin 2) (L' ⊗[K'] A'))) τ₀' =
        Measure.map (fun t : twistedCentralizer K L A σ δ =>
          Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := borel _
       letI := centralizerBorel A γ
       letI := twistedCentralizerBorel K L A σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) A =>
               Y.map (fun x : A => ((1 : L) ⊗ₜ[K] x : L ⊗[K] A))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X.map (sigmaTensor K L A σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) =>
             ((t : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).map
               (fun x : A => ((1 : L) ⊗ₜ[K] x : L ⊗[K] A))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] A) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L A σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] A) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) := borel _;
       letI := centralizerBorel A' γ';
       letI := twistedCentralizerBorel K' L' A' σ' δ';
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A'))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A'))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) A' =>
               Y.map (fun x : A' => ((1 : L') ⊗ₜ[K'] x : L' ⊗[K'] A'))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A'))) =
             {X | X * (δ' : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) =
               (δ' : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) * X.map (sigmaTensor K' L' A' σ')} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A'))) =>
             ((t : GL (Fin 2) A') : Matrix (Fin 2) (Fin 2) A').map
               (fun x : A' => ((1 : L') ⊗ₜ[K'] x : L' ⊗[K'] A'))) τ₀ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L' ⊗[K'] A') (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A') =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K' L' A' σ' δ') =>
             ((t : GL (Fin 2) (L' ⊗[K'] A')) : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A'))) τ₀' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L' ⊗[K'] A') (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A') =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_gram_map_of_ringEquiv_of_exists_gram.solution
