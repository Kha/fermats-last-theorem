import Mathlib.Analysis.SpecialFunctions.Complex.Log
import P2M.Util
import P2M.Sol.S_Complex_log_add_log_eq_log_sub_of_re_pos

theorem Complex.log_add_log_eq_log_sub_of_re_pos {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.log u + Complex.log v = Complex.log w - Real.pi * Complex.I / 2 := by p2m_exact_reverting @_root_.P2MW.S_Complex_log_add_log_eq_log_sub_of_re_pos.solution
