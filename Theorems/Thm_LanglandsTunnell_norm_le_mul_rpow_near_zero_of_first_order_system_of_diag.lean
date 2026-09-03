import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
    (m : ℕ) (a : Fin m → ℂ) (r₀ c τ : ℝ) (hτ : 0 < τ) (ha : ∀ i, r₀ ≤ (a i).re)
    (B : ℝ → Matrix (Fin m) (Fin m) ℂ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, ‖B y i j‖ ≤ c * y ^ τ)
    (F : Fin m → ℝ → ℂ) (hF : ∀ i, DifferentiableOn ℝ (F i) (Set.Ioi 0))
    (hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i,
      (y : ℂ) * deriv (F i) y = a i * F i y + ∑ j, B y i j * F j y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖F i y‖ ≤ C * y ^ (r₀ - ε) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag.solution
