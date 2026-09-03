import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_Matrix_hasDistinctRationalEigenvalues_of_isConj

theorem Matrix.hasDistinctRationalEigenvalues_of_isConj {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (h : IsConj M N)
    (hM : M.HasDistinctRationalEigenvalues) : N.HasDistinctRationalEigenvalues := by p2m_exact_reverting @_root_.P2MW.S_Matrix_hasDistinctRationalEigenvalues_of_isConj.solution
