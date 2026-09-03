import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [Finite (MaximalSpectrum A)]
    (ι : L →ₐ[K] A)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μL)
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA)

    (hsec : ∀ γ : GL (Fin 2) A, AutomorphicForm.IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ →
      ∀ f : GL (Fin 2) A → ℂ, HasCompactSupport f →
        ∃ w : GL (Fin 2) A → ℝ, AutomorphicForm.IsSectionFnOn A γ τ f w ∧ Continuous w)

    (hμAr : @Measure.IsMulRightInvariant (GL (Fin 2) A) (AutomorphicForm.glBorelOf A) _ μA) :
    ∃ c : ℝ, 0 < c ∧
      ∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → HasCompactSupport φ →
        (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (γ : GL (Fin 2) A), AutomorphicForm.IsRegularSemisimple γ →
          ∀ y : GL (Fin 2) (L ⊗[K] A), AutomorphicForm.IsNormConjugator K L A σ γ δ y →
          ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
                (AutomorphicForm.centralizerBorel A γ))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L A σ δ)),
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ →
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ' →
            AutomorphicForm.Coupled K L A σ γ δ y τ τ' →
            ∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μL δ τ' φ I' →
              AutomorphicForm.IsOrbitalIntegralOn A μA γ τ
                (c • AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ) I') ∧
        (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (z : Aˣ) (y : GL (Fin 2) (L ⊗[K] A)),
          AutomorphicForm.IsNormConjugator K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) δ y →
          ∀ (τ : @Measure (Subgroup.centralizer
                  ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)))
                (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L A σ δ)),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) τ →
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ' →
            AutomorphicForm.Coupled K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) δ y τ τ' →
            ∀ c₀ : NNReal,
              @Measure.map _ _
                  (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
                  (AutomorphicForm.glBorelOf A) Subtype.val τ = c₀ • μA →
              ∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μL δ τ' φ I' →
                I' = (c • AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ)
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z) * ((((c₀ : ℝ))⁻¹ : ℝ) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.solution
