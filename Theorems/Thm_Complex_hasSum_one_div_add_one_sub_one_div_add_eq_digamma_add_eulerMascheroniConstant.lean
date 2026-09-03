import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant

set_option autoImplicit false

theorem Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s))
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant.solution
