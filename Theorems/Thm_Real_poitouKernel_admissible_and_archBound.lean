import Mathlib
import P2M.Util
import P2M.Sol.S_Real_poitouKernel_admissible_and_archBound

theorem Real.poitouKernel_admissible_and_archBound :
    let F : ℝ → ℝ := fun x => Real.exp (-(11 / 100) * x ^ 2) / Real.cosh (x / 2)

    Differentiable ℝ F ∧ (∀ x : ℝ, F (-x) = F x) ∧ F 0 = 1 ∧ (∀ x : ℝ, 0 ≤ F x) ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧

    (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      0 ≤ ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x)) ∧

    ContDiff ℝ 2 F ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧

    (2 * ∫ x in Set.Ioi (0 : ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2)))
        = 2 * Real.sqrt (100 * Real.pi / 11)) ∧

    (Real.log (9805 / 2000) + (1 / 12) * Real.sqrt (100 * Real.pi / 11)
      ≤ Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
          - ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2)))) := by p2m_exact_reverting @_root_.P2MW.S_Real_poitouKernel_admissible_and_archBound.solution
