import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_contDiffAt_of_mdifferentiable_im_cpow_mul_of_weight_of_central

set_option autoImplicit false

open scoped Manifold

theorem AutomorphicForm.contDiffAt_of_mdifferentiable_im_cpow_mul_of_weight_of_central
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ : ℝ,
      F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F m)
    (hc : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ t : ℝ, 0 < t →
      F (t • m) = ((t : ℂ) ^ c₀) * F m)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)))
    (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : 0 < m.det) :
    ContDiffAt ℝ (⊤ : ℕ∞) F m := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_contDiffAt_of_mdifferentiable_im_cpow_mul_of_weight_of_central.solution
