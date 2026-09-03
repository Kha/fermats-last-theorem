import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_Matrix_trace_pow_eq_sum_pow

theorem Matrix.trace_pow_eq_sum_pow {R : Type*} [CommRing R]
    {M : Matrix (Fin 2) (Fin 2) R} {α β : R}
    (htr : M.trace = α + β) (hdet : M.det = α * β) (k : ℕ) :
    (M ^ k).trace = α ^ k + β ^ k := by p2m_exact_reverting @_root_.P2MW.S_Matrix_trace_pow_eq_sum_pow.solution
