import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ArchWeightOne_central_eq_coe_of_forall_mdifferentiable

set_option autoImplicit false

open scoped Manifold

theorem AutomorphicForm.ArchWeightOne.central_eq_coe_of_forall_mdifferentiable
    (F : GL (Fin 2) ℝ → ℂ) (ω : ℝˣ → ℂ)
    (hrot : ∀ (g : GL (Fin 2) ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1),
      F (g * Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
        (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
            exact one_ne_zero)) = (⟨a, b⟩ : ℂ) * F g)
    (hcen : ∀ (g : GL (Fin 2) ℝ) (t : ℝˣ), 0 < (t : ℝ) →
      F (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ω t * F g)
    (hhol : ∀ m : GL (Fin 2) ℝ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * F (m * Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by simp [Matrix.det_fin_two_of]; exact z.im_ne_zero)))
    (hne : ∃ g : GL (Fin 2) ℝ, F g ≠ 0)
    (t : ℝˣ) (ht : 0 < (t : ℝ)) :
    ω t = ((t : ℝ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ArchWeightOne_central_eq_coe_of_forall_mdifferentiable.solution
