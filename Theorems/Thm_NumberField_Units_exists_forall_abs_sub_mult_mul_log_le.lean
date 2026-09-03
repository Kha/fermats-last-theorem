import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import P2M.Util
import P2M.Sol.S_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le

theorem NumberField.Units.exists_forall_abs_sub_mult_mul_log_le (K : Type*) [Field K]
    [NumberField K] : ∃ R : ℝ, ∀ t : NumberField.InfinitePlace K → ℝ, ∑ w, t w = 0 →
      ∃ u : (NumberField.RingOfIntegers K)ˣ, ∀ w : NumberField.InfinitePlace K,
        |t w - (w.mult : ℝ) * Real.log (w (u : K))| ≤ R := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le.solution
