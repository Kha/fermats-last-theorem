import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import P2M.Util
import P2M.Sol.S_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one

theorem Matrix.det_eq_zero_of_isIdempotentElem_of_trace_eq_one {A : Type*} [CommRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : IsIdempotentElem e) (htr : e.trace = 1) :
    e.det = 0 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one.solution
