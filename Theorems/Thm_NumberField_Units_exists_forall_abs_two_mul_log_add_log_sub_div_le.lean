import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import P2M.Util
import P2M.Sol.S_NumberField_Units_exists_forall_abs_two_mul_log_add_log_sub_div_le

set_option autoImplicit false

open NumberField

theorem NumberField.Units.exists_forall_abs_two_mul_log_add_log_sub_div_le
    (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, ∀ r : InfinitePlace F → ℝ, (∀ w, 0 < r w) →
      ∃ ε : (𝓞 F)ˣ, ∀ w : InfinitePlace F,
        |2 * Real.log (w (algebraMap (𝓞 F) F ε)) + Real.log (r w)
            - (∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log (r w')) / (Module.finrank ℚ F)| ≤ C := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Units_exists_forall_abs_two_mul_log_add_log_sub_div_le.solution
