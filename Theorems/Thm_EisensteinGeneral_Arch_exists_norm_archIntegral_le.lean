import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import P2M.Util
import P2M.Sol.S_EisensteinGeneral_Arch_exists_norm_archIntegral_le

open Set MeasureTheory
set_option autoImplicit false

theorem EisensteinGeneral.Arch.exists_norm_archIntegral_le (c : ℂ) (hc : 0 < c.re) (M : ℝ) :
    ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (z : ℂ) (r : ℝ), |z.re| ≤ M → r ≠ 0 →
      ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ C * max 1 (|r| ^ (-(N : ℝ))) * Real.exp (-c' * |r|) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinGeneral_Arch_exists_norm_archIntegral_le.solution
