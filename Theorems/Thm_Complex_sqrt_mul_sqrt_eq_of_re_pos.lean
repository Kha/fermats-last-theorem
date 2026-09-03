import Mathlib.Analysis.RCLike.Sqrt
import P2M.Util
import P2M.Sol.S_Complex_sqrt_mul_sqrt_eq_of_re_pos

theorem Complex.sqrt_mul_sqrt_eq_of_re_pos {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.sqrt u * Complex.sqrt v = Complex.sqrt (-Complex.I) * Complex.sqrt w := by p2m_exact_reverting @_root_.P2MW.S_Complex_sqrt_mul_sqrt_eq_of_re_pos.solution
