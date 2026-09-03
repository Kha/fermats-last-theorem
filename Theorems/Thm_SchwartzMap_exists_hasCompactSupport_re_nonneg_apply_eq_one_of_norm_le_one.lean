import Mathlib
import P2M.Util
import P2M.Sol.S_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one

set_option autoImplicit false

open scoped SchwartzMap

theorem SchwartzMap.exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ g : 𝓢(E, ℂ), HasCompactSupport g ∧ (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → g x = 1) ∧ (∀ x, 2 ≤ ‖x‖ → g x = 0) := by p2m_exact_reverting @_root_.P2MW.S_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one.solution
