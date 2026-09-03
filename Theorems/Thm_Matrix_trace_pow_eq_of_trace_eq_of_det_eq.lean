import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_Matrix_trace_pow_eq_of_trace_eq_of_det_eq

theorem Matrix.trace_pow_eq_of_trace_eq_of_det_eq {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (htr : M.trace = N.trace) (hdet : M.det = N.det)
    (k : ℕ) : (M ^ k).trace = (N ^ k).trace := by p2m_exact_reverting @_root_.P2MW.S_Matrix_trace_pow_eq_of_trace_eq_of_det_eq.solution
