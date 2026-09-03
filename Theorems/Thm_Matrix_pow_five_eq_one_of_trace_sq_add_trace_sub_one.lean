import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import P2M.Util
import P2M.Sol.S_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one

theorem Matrix.pow_five_eq_one_of_trace_sq_add_trace_sub_one {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) (hdet : g.det = 1) (ht : g.trace ^ 2 + g.trace - 1 = 0) : g ^ 5 = 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one.solution
