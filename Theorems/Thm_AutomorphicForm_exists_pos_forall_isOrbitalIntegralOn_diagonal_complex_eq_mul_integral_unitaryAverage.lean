import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage
    (μ : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μ)
    (a₁ a₂ : ℂ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (γ : GL (Fin 2) ℂ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂])
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ f : GL (Fin 2) ℂ → ℂ, Continuous f → HasCompactSupport f →
        ∀ I : ℂ, IsOrbitalIntegralOn ℂ μ γ τ f I →
          I = (κ : ℂ) * ∫ v : ℂ, unitaryAverage (fun k =>
            if h : Matrix.det !![a₁, v; 0, a₂] ≠ 0 then
              f (k⁻¹ * Matrix.GeneralLinearGroup.mkOfDetNeZero _ h * k) else 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage.solution
