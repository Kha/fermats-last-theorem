import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_semilocal_central_transfer_peel_step

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.semilocal_central_transfer_peel_step
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, SecondCountableTopology (A i)]
    (X Y : ι → Type) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)] [∀ i, FiniteDimensional ℝ (X i)]
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)] [∀ i, FiniteDimensional ℝ (Y i)]
    (εK : ∀ i, GL (Fin 2) (A i) → X i) (hεK : ∀ i, Continuous (εK i))
    (εL : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Y i) (hεL : ∀ i, Continuous (εL i))
    (c : ∀ i, (A i)ˣ)
    (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
    (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
    (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))
    (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
    (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))

    (hsecK : ∀ (i : ι) (γ : GL (Fin 2) (A i)), IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      ∀ f : GL (Fin 2) (A i) → ℂ, Continuous f → HasCompactSupport f →
        ∃ w : GL (Fin 2) (A i) → ℝ, IsSectionFnOn (A i) γ τ f w ∧ Continuous w)
    (hsecL : ∀ (i : ι) (δ : GL (Fin 2) (L ⊗[K] A i)),
      (IsRegularSemisimple (normString K L (A i) σ δ) ∨
        ∃ d : (L ⊗[K] A i)ˣ, IsSigmaConjugate K L (A i) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
      ∀ φ : GL (Fin 2) (L ⊗[K] A i) → ℂ, Continuous φ → HasCompactSupport φ →
        ∃ W : GL (Fin 2) (L ⊗[K] A i) → ℝ, IsTwistedSectionFnOn K L (A i) σ δ τ' φ W ∧ Continuous W)

    (heng : ∀ (i : ι) (φ : GL (Fin 2) (L ⊗[K] A i) → ℂ),
      ((∃ Φ₁ : Y i → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (εL i g)) ∧ HasCompactSupport φ) →
      ∀ (f : GL (Fin 2) (A i) → ℂ),
      ((∃ F₁ : X i → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, f g = F₁ (εK i g)) ∧ HasCompactSupport f) →
      (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)),
        ∀ δ : GL (Fin 2) (L ⊗[K] A i), IsRegularSemisimple (normString K L (A i) σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] A i), IsNormConjugator K L (A i) σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ))
          (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
          Coupled K L (A i) σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
            IsOrbitalIntegralOn (A i) (μ i) γ τ f I → I' = I) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] A i),
        IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)} : Set (GL (Fin 2) (A i))))
              (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))))
          (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
          @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
          Coupled K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
            IsOrbitalIntegralOn (A i) (μ i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) τ f I → I' = I)

    (ν : @Measure ((i : ι) → GL (Fin 2) (A i)) (borel _)) (hν : @Measure.IsHaarMeasure ((i : ι) → GL (Fin 2) (A i)) _ _ (borel _) ν)
    (ν' : @Measure ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) (borel _)) (hν' : @Measure.IsHaarMeasure ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) _ _ (borel _) ν')
    (F : ((i : ι) → GL (Fin 2) (A i)) → ℂ)
    (hF : (∃ F₁ : ((i : ι) → X i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, F g = F₁ (fun i => εK i (g i))) ∧
      HasCompactSupport F)
    (Φ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ)
    (hΦ : (∃ Φ₁ : ((i : ι) → Y i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, Φ g = Φ₁ (fun i => εL i (g i))) ∧
      HasCompactSupport Φ)

    (hreg : ∀ (γ : ((i : ι) → GL (Fin 2) (A i))) (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsRegularSemisimple (γ i)) → (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      (∀ i, IsNormConjugator K L (A i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i))) => fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
        ∀ I I' : ℂ,
          (∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
            (∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
            I' = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
          (∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
            (∀ x : ((i : ι) → GL (Fin 2) (A i)), F (x⁻¹ * γ * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) ∧
            I = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (A i))) ν (fun x => F (x⁻¹ * γ * x) * (w x : ℂ))) →
          I' = I)

    (ih : ∀ {κ : Type} [Fintype κ] [DecidableEq κ]
      (A : κ → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
      [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
      [∀ i, SecondCountableTopology (A i)]
      (X Y : κ → Type) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)] [∀ i, FiniteDimensional ℝ (X i)]
      [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)] [∀ i, FiniteDimensional ℝ (Y i)]
      (εK : ∀ i, GL (Fin 2) (A i) → X i) (hεK : ∀ i, Continuous (εK i))
      (εL : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Y i) (hεL : ∀ i, Continuous (εL i))
      (c : ∀ i, (A i)ˣ)
      (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
      (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
      (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))
      (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
      (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))
      (hsecK : ∀ (i : κ) (γ : GL (Fin 2) (A i)), IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      ∀ f : GL (Fin 2) (A i) → ℂ, Continuous f → HasCompactSupport f →
      ∃ w : GL (Fin 2) (A i) → ℝ, IsSectionFnOn (A i) γ τ f w ∧ Continuous w)
      (hsecL : ∀ (i : κ) (δ : GL (Fin 2) (L ⊗[K] A i)),
      (IsRegularSemisimple (normString K L (A i) σ δ) ∨
      ∃ d : (L ⊗[K] A i)ˣ, IsSigmaConjugate K L (A i) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
      @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
      ∀ φ : GL (Fin 2) (L ⊗[K] A i) → ℂ, Continuous φ → HasCompactSupport φ →
      ∃ W : GL (Fin 2) (L ⊗[K] A i) → ℝ, IsTwistedSectionFnOn K L (A i) σ δ τ' φ W ∧ Continuous W)
      (heng : ∀ (i : κ) (φ : GL (Fin 2) (L ⊗[K] A i) → ℂ),
      ((∃ Φ₁ : Y i → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (εL i g)) ∧ HasCompactSupport φ) →
      ∀ (f : GL (Fin 2) (A i) → ℂ),
      ((∃ F₁ : X i → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, f g = F₁ (εK i g)) ∧ HasCompactSupport f) →
      (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)),
      ∀ δ : GL (Fin 2) (L ⊗[K] A i), IsRegularSemisimple (normString K L (A i) σ δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (L ⊗[K] A i), IsNormConjugator K L (A i) σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ))
      (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
      Coupled K L (A i) σ γ δ y τ τ' →
      ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
      IsOrbitalIntegralOn (A i) (μ i) γ τ f I → I' = I) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] A i),
      IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)} : Set (GL (Fin 2) (A i))))
      (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))))
      (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))) τ →
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
      @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
      Coupled K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y τ τ' →
      ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
      IsOrbitalIntegralOn (A i) (μ i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) τ f I → I' = I)
      (ν : @Measure ((i : κ) → GL (Fin 2) (A i)) (borel _)) (hν : @Measure.IsHaarMeasure ((i : κ) → GL (Fin 2) (A i)) _ _ (borel _) ν)
      (ν' : @Measure ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) (borel _)) (hν' : @Measure.IsHaarMeasure ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) _ _ (borel _) ν')
      (F : ((i : κ) → GL (Fin 2) (A i)) → ℂ)
      (hF : (∃ F₁ : ((i : κ) → X i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, F g = F₁ (fun i => εK i (g i))) ∧
      HasCompactSupport F)
      (Φ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ)
      (hΦ : (∃ Φ₁ : ((i : κ) → Y i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, Φ g = Φ₁ (fun i => εL i (g i))) ∧
      HasCompactSupport Φ)
      (hreg : ∀ (γ : ((i : κ) → GL (Fin 2) (A i))) (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsRegularSemisimple (γ i)) → (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      (∀ i, IsNormConjugator K L (A i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i))) => fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ I I' : ℂ,
      (∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
      (∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      I' = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
      (∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
      (∀ x : ((i : κ) → GL (Fin 2) (A i)), F (x⁻¹ * γ * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1) ∧
      I = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (A i))) ν (fun x => F (x⁻¹ * γ * x) * (w x : ℂ))) →
      I' = I),
      Fintype.card κ < Fintype.card ι →
      (∀ (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer
      ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer
      ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i))) =>
      fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ I I' : ℂ,
      (∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
      (∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      I' = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
      (∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
      (∀ x : ((i : κ) → GL (Fin 2) (A i)), F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1) ∧
      I = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (A i))) ν
      (fun x => F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) * (w x : ℂ))) →
      I' = I) ∧
      (∀ (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i))) =>
      fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      (∀ (δ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))), (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      ∀ (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      (∀ (γ : ((i : κ) → GL (Fin 2) (A i))), (∀ i, IsRegularSemisimple (γ i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
      ∀ x : ((i : κ) → GL (Fin 2) (A i)), Ψ (x⁻¹ * γ * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1)) :
    (∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer
                ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i))) =>
              fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
        ∀ I I' : ℂ,
          (∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
            (∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
            I' = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
          (∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
            (∀ x : ((i : ι) → GL (Fin 2) (A i)), F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) ∧
            I = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (A i))) ν
              (fun x => F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) * (w x : ℂ))) →
          I' = I) ∧
    (∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i))) =>
              fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
    (∀ (δ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))), (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      ∀ (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
    (∀ (γ : ((i : ι) → GL (Fin 2) (A i))), (∀ i, IsRegularSemisimple (γ i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
            ∀ x : ((i : ι) → GL (Fin 2) (A i)), Ψ (x⁻¹ * γ * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.solution
