import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_eq_neg_half_add_mul_I_of_powerSum_symmetry_of_re_eq_neg_half

set_option autoImplicit false

theorem
LanglandsTunnell.CubicInduction.exists_eq_neg_half_add_mul_I_of_powerSum_symmetry_of_re_eq_neg_half
    (ν : Fin 3 → ℂ)
    (h1 : (∑ a, ν a).re = 0) (h2 : (∑ a, ν a ^ 2).im = 0) (h3 : (∑ a, ν a ^ 3).re = 0)
    (a₀ : Fin 3) (ha₀ : (ν a₀).re = -1 / 2) :
    ∃ (σ σ₃ : ℝ) (b c : Fin 3), b ≠ a₀ ∧ c ≠ a₀ ∧ b ≠ c ∧
      ν a₀ = -1 / 2 + σ * Complex.I ∧ ν b = 1 / 2 + σ * Complex.I ∧ ν c = σ₃ * Complex.I := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_neg_half_add_mul_I_of_powerSum_symmetry_of_re_eq_neg_half.solution
