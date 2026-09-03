import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ArchWeightOne_intervalIntegral_exp_neg_mul_translate_rotation_eq

set_option autoImplicit false

open scoped Manifold

theorem AutomorphicForm.ArchWeightOne.intervalIntegral_exp_neg_mul_translate_rotation_eq
    (F : GL (Fin 2) ℝ → ℂ) (hF : Continuous F)
    (hrot : ∀ (g : GL (Fin 2) ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1),
      F (g * Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
        (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
            exact one_ne_zero)) = (⟨a, b⟩ : ℂ) * F g)
    (hcen : ∀ (g : GL (Fin 2) ℝ) (t : ℝˣ), 0 < (t : ℝ) →
      F (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((t : ℝ) : ℂ) * F g)
    (hhol : ∀ m : GL (Fin 2) ℝ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * F (m * Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by simp [Matrix.det_fin_two_of]; exact z.im_ne_zero)))
    (h g : GL (Fin 2) ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(θ * Complex.I)) *
        F (g * Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
          (by rw [Matrix.det_fin_two_of, show Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ
                = Real.cos θ ^ 2 + Real.sin θ ^ 2 by ring, Real.cos_sq_add_sin_sq]
              exact one_ne_zero) * h)) =
      (if 0 < ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) then
          2 * Real.pi * (2 * (((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) : ℂ) /
            (((h 0 0 + h 1 1 : ℝ) : ℂ) + ((h 1 0 - h 0 1 : ℝ) : ℂ) * Complex.I))
        else 0) * F g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ArchWeightOne_intervalIntegral_exp_neg_mul_translate_rotation_eq.solution
