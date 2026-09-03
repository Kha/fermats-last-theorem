import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_lintegral_inv_sq_quadForm_shell_eq

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.lintegral_inv_sq_quadForm_shell_eq
    (c : ℝ) (hc : c < 0) :
    ∫⁻ a in {a : Fin 4 → ℝ | a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2) ∈ Set.Icc (1 : ℝ) (Real.exp 2)},
        (ENNReal.ofReal ((a 0 ^ 2 + a 1 ^ 2 - c * (a 2 ^ 2 + a 3 ^ 2)) ^ 2))⁻¹ =
      ENNReal.ofReal (2 * Real.pi ^ 2 / |c|) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_lintegral_inv_sq_quadForm_shell_eq.solution
