import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_Matrix_hasDistinctRationalEigenvalues_pow

theorem Matrix.hasDistinctRationalEigenvalues_pow {𝕜 : Type*} [Field 𝕜]
    {M : Matrix (Fin 2) (Fin 2) 𝕜} {d : ℕ} (hd : 0 < d) (hM : M ^ d = 1)
    (h : M.HasDistinctRationalEigenvalues) {k : ℕ} (hk : k.Coprime d) :
    (M ^ k).HasDistinctRationalEigenvalues := by p2m_exact_reverting @_root_.P2MW.S_Matrix_hasDistinctRationalEigenvalues_pow.solution
