import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_archTermDerived_le_log_abs_discr

theorem NumberField.archTermDerived_le_log_abs_discr
    (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (F : ℝ → ℝ)
    (h1 : Differentiable ℝ F) (h2 : ∀ x : ℝ, F (-x) = F x) (h3 : F 0 = 1) (h4 : ∀ x : ℝ, 0 ≤ F x)
    (h5 : ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))
    (h6 : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      0 ≤ ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x))
    (h7 : ContDiff ℝ 2 F)
    (h8 : ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) :
    ((Module.finrank ℚ K : ℝ) * (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
        - ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2))))
      - 2 * ∫ x in Set.Ioi (0 : ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2))))
      + (Module.finrank ℚ K : ℝ) * Real.log 2 ≤ Real.log |(NumberField.discr K : ℝ)| := by p2m_exact_reverting @_root_.P2MW.S_NumberField_archTermDerived_le_log_abs_discr.solution
