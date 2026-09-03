import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : ∀ g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      @Measure.map _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)) (fun z => g * z) μ = μ)
    (c : ℝˣ) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (hC : Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ') :
    0 < (c : ℝ) ∧
    ∃ d : ℝˣ, (d : ℝ) * d = c ∧
      ∃ τ₁ : @Measure
          (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))),
        @Measure.IsHaarMeasure _ _ _
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ₁ ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
          (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) 1 τ τ₁ ∧
        ∀ (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (I : ℂ),
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ' φ I ↔
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ
              (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ₁ φ I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe.solution
