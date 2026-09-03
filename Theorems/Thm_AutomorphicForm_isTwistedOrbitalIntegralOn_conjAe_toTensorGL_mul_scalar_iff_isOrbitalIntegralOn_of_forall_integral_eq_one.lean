import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar_iff_isOrbitalIntegralOn_of_forall_integral_eq_one

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar_iff_isOrbitalIntegralOn_of_forall_integral_eq_one
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (d : ℝˣ)
    (hι : Topology.IsClosedEmbedding (toTensorGL ℝ ℂ ℝ))
    (t : GL (Fin 2) ℝ) (ht : t = 1 ∨ IsRegularSemisimple t)
    (hT : ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe
          (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) ↔
        ∃ m : GL (Fin 2) ℝ, m ∈ Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ∧ x = toTensorGL ℝ ℂ ℝ m)
    (α : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hαc : Continuous α) (hαs : HasCompactSupport α) (hα0 : ∀ x, 0 ≤ α x)
    (hαn : ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom (x⁻¹ * toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ≠ 0 →
        ∫ m, α (toTensorGL ℝ ℂ ℝ m * x) ∂μA = 1)
    (ψ : GL (Fin 2) ℝ → ℂ) (hψc : Continuous ψ)
    (hψ : ∀ s : GL (Fin 2) ℝ, ψ s = ∫ x, (α x : ℂ) *
      φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom (x⁻¹ * toTensorGL ℝ ℂ ℝ (s * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∂μL)
    (τ : @Measure (Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ t))
    (τ' : @Measure
      (twistedCentralizer ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ t) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ')
    (hcpl : Coupled ℝ ℂ ℝ Complex.conjAe t
      (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) 1 τ τ')
    (I' : ℂ) :
    IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ'
        (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' ↔
      IsOrbitalIntegralOn ℝ μA t τ ψ I' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar_iff_isOrbitalIntegralOn_of_forall_integral_eq_one.solution
