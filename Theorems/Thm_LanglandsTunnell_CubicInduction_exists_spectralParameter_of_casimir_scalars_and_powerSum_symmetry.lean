import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_spectralParameter_of_casimir_scalars_and_powerSum_symmetry

set_option autoImplicit false

theorem
LanglandsTunnell.CubicInduction.exists_spectralParameter_of_casimir_scalars_and_powerSum_symmetry
    (lam₁ lam₂ lam₃ : ℂ) :
    (∃ ν : Fin 3 → ℂ,
      lam₁ = ∑ a, ν a ∧
      lam₂ = (∑ a, ν a ^ 2) - 2 ∧
      lam₃ = (∑ a, ν a ^ 3) + (∑ a, ν a ^ 2) - (ν 0 * ν 1 + ν 0 * ν 2 + ν 1 * ν 2) - 2 * (∑ a, ν a) - 3) ∧
    ∀ ν : Fin 3 → ℂ,
      lam₁ = ∑ a, ν a →
      lam₂ = (∑ a, ν a ^ 2) - 2 →
      lam₃ = (∑ a, ν a ^ 3) + (∑ a, ν a ^ 2) - (ν 0 * ν 1 + ν 0 * ν 2 + ν 1 * ν 2) - 2 * (∑ a, ν a) - 3 →
      lam₁.re = 0 → lam₂.im = 0 → lam₃ + (starRingEnd ℂ) (lam₃ + lam₁ ^ 2 - 3 * lam₂) = 0 →
      (∑ a, ν a).re = 0 ∧ (∑ a, ν a ^ 2).im = 0 ∧ (∑ a, ν a ^ 3).re = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_spectralParameter_of_casimir_scalars_and_powerSum_symmetry.solution
