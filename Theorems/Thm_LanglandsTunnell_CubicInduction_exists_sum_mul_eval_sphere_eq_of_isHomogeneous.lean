import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.exists_sum_mul_eval_sphere_eq_of_isHomogeneous
    (ℓ : ℕ) (Λ : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] ℂ) :
    ∃ (N : ℕ) (u : Fin N → Fin 3 → ℝ) (c : Fin N → ℂ),
      (∀ n : Fin N, ∑ a : Fin 3, u n a ^ 2 = 1) ∧
      ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
        Λ p = ∑ n : Fin N, c n * MvPolynomial.eval (fun a : Fin 3 => ((u n a : ℝ) : ℂ)) p := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous.solution
