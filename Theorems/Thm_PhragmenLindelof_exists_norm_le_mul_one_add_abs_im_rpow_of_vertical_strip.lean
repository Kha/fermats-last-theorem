import Mathlib
import P2M.Util
import P2M.Sol.S_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip

set_option autoImplicit false

theorem PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
    (a b α : ℝ) (hab : a < b) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
        (∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
            ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|))) →
        (∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        (∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * M * (1 + |z.im|) ^ α := by p2m_exact_reverting @_root_.P2MW.S_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip.solution
