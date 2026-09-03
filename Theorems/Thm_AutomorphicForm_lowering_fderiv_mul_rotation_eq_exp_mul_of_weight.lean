import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight

set_option autoImplicit false

theorem AutomorphicForm.lowering_fderiv_mul_rotation_eq_exp_mul_of_weight
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ)
    (hF : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → DifferentiableAt ℝ F m)
    (hk : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ : ℝ,
      F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F m)
    (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : 0 < m.det) (θ : ℝ) :
    (fderiv ℝ F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
          ((m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) * !![1, 0; 0, -1]) -
        Complex.I *
          fderiv ℝ F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
            ((m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) * !![0, 1; 1, 0])) / 2 =
      Complex.exp (Complex.I * (k - 2) * θ) *
        ((fderiv ℝ F m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ F m (m * !![0, 1; 1, 0])) / 2) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight.solution
