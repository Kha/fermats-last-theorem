import Mathlib
import P2M.Util
import P2M.Sol.S_IsNonarchimedean_apply_le_one_of_isIntegral_int

set_option autoImplicit false

theorem IsNonarchimedean.apply_le_one_of_isIntegral_int
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {x : K} (hx : IsIntegral ℤ x) : μ x ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_IsNonarchimedean_apply_le_one_of_isIntegral_int.solution
