import Mathlib
import P2M.Util
import P2M.Sol.S_AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm

set_option autoImplicit false

theorem AbsoluteValue.Completion.norm_coe_and_exists_one_lt_norm
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    (∀ x : K, ‖(x : v.Completion)‖ = v x) ∧ (v.IsNontrivial → ∃ x : v.Completion, 1 < ‖x‖) := by p2m_exact_reverting @_root_.P2MW.S_AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm.solution
