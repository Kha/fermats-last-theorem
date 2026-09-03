import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one

set_option autoImplicit false

universe u
theorem Matrix.exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one {A : Type u} [CommRing A] [IsLocalRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : e * e = e) (htr : e.trace = 1) :
    ∃ u w : Fin 2 → A, IsUnit (Matrix.of (fun i j => ![u, w] j i)).det ∧
      e.mulVec u = u ∧ e.mulVec w = 0 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one.solution
