import Mathlib
import P2M.Util
import P2M.Sol.S_AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean

set_option autoImplicit false

theorem AbsoluteValue.Completion.isUltrametricDist_of_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    IsUltrametricDist v.Completion := by p2m_exact_reverting @_root_.P2MW.S_AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean.solution
