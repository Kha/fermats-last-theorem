import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (m : ℕ) (f : GL (Fin 2) ℝ → ℂ), Continuous f → HasCompactSupport f →
      (∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
        f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
          ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g) →
      ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ r : ℝ, 0 < r →
        (∫ θ in (0 : ℝ)..Real.pi,
            ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
          -(κ : ℂ) * (1 / r : ℂ) *
            ∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) *
              (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
                (-1 : ℂ) ^ j * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.solution
