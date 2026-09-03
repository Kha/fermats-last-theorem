import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq

set_option autoImplicit false

open scoped Manifold

theorem AutomorphicForm.mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hF : ∀ z : UpperHalfPlane,
      DifferentiableAt ℝ F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
    (hk : ∀ (z : UpperHalfPlane) (θ : ℝ),
      F ((!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *
          !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
    (hc : ∀ (z : UpperHalfPlane) (t : ℝ), 0 < t →
      F (t • (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) =
        ((t : ℂ) ^ c₀) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane =>
        (((z.im : ℝ) : ℂ) ^ σ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) ↔
      ∀ z : UpperHalfPlane,
        (fderiv ℝ F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
              ((!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, -1]) -
            Complex.I *
              fderiv ℝ F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
                ((!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 1, 0])) / 2 =
          -(σ + (k + c₀) / 2) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq.solution
