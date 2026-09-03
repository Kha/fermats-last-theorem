import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (d : ℝˣ) :
    ∃ ψ : GL (Fin 2) ℝ → ℂ,
      ((∃ Ψ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        ∀ g, ψ g = Ψ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport ψ) ∧
      ∃ U ∈ nhds (1 : GL (Fin 2) ℝ), ∀ t ∈ U, (t = 1 ∨ IsRegularSemisimple t) →
        ∀ (τ : @Measure (Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ t))
          (τ' : @Measure
            (twistedCentralizer ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)))),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ t) τ →
          @Measure.IsHaarMeasure _ _ _
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe t (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))
            1 τ τ' →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' ↔
            IsOrbitalIntegralOn ℝ μA t τ ψ I' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar.solution
