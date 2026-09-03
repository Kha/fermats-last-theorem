import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φv fv)
    (ν : (GL (Fin 2) (v.adicCompletion K) → ℂ) → ℂ)
    (hν : ∀ (γ₀ : GL (Fin 2) (v.adicCompletion K)), AutomorphicForm.IsRegularSemisimple γ₀ →
        ∀ (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v)),
        ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),

          (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
            letI := AutomorphicForm.localGLBorel K v
            ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
              ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
              ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
                @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
                @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                    Subtype.val τ = νT →
                ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
                  I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) + B γ * ν f) ∧

          (((γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
              (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) →
            (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
                (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                  Subtype.val νT)) →
            A = 0 ∧
            letI := AutomorphicForm.localGLBorel K v
            ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
              ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ → B γ ≠ 0) ∧

          ((∀ g : GL (Fin 2) (v.adicCompletion K),
              ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
                 ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) →
            (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
                (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                  Subtype.val νT)) →
            A ≠ 0)) :
    ν fv = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.solution
