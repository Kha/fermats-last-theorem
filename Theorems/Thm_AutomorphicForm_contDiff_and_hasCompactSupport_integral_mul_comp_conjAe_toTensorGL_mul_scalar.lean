import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (d : ℝˣ)
    (α : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hαc : Continuous α) (hαs : HasCompactSupport α)
    (ψ : GL (Fin 2) ℝ → ℂ)
    (hψ : ∀ s : GL (Fin 2) ℝ, ψ s = ∫ x, (α x : ℂ) *
      φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom (x⁻¹ * toTensorGL ℝ ℂ ℝ (s * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∂μL) :
    (∃ Ψ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        ∀ g, ψ g = Ψ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport ψ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar.solution
