import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero

theorem Matrix.isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero
    {R : Type*} [CommRing R] (e : Matrix (Fin 2) (Fin 2) R) (htr : e.trace = 1) (hdet : e.det = 0) :
    e * e = e ∧
      IsCompl (LinearMap.range (Matrix.mulVecLin e)) (LinearMap.range (Matrix.mulVecLin (1 - e))) ∧
      Module.Invertible R ↥(LinearMap.range (Matrix.mulVecLin e)) ∧
      Module.Invertible R ↥(LinearMap.range (Matrix.mulVecLin (1 - e))) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero.solution
