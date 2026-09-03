import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_setIntegral_image_ellipticCoords_eq_integral_jacobian_smul

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.GL2Real.setIntegral_image_ellipticCoords_eq_integral_jacobian_smul
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ))
    (hΨ : ∀ v, Ψ v =
      ((v.1.1 * Real.cos v.1.2 - v.1.1 * Real.sin v.1.2 * v.2.1 / v.2.2,
          v.1.1 * Real.sin v.1.2 * (v.2.1 ^ 2 + v.2.2 ^ 2) / v.2.2),
        (-(v.1.1 * Real.sin v.1.2) / v.2.2,
          v.1.1 * Real.cos v.1.2 + v.1.1 * Real.sin v.1.2 * v.2.1 / v.2.2)))
    (D : Set ((ℝ × ℝ) × (ℝ × ℝ)))
    (hD : D = {v | 0 < v.1.1 ∧ v.1.2 ∈ Set.Ioo (-Real.pi) Real.pi ∧ v.1.2 ≠ 0 ∧ 0 < v.2.2})
    (f : (ℝ × ℝ) × (ℝ × ℝ) → F) :
    Set.InjOn Ψ D ∧ MeasurableSet (Ψ '' D) ∧
      (IntegrableOn f (Ψ '' D) ↔
        IntegrableOn (fun v => (4 * v.1.1 ^ 3 * Real.sin v.1.2 ^ 2 / v.2.2 ^ 2) • f (Ψ v)) D) ∧
      ∫ w in Ψ '' D, f w = ∫ v in D, (4 * v.1.1 ^ 3 * Real.sin v.1.2 ^ 2 / v.2.2 ^ 2) • f (Ψ v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_setIntegral_image_ellipticCoords_eq_integral_jacobian_smul.solution
