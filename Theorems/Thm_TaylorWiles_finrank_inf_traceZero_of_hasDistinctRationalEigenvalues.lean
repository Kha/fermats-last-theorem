import Mathlib
import Definitions.Def_Deformations_TaylorWilesLocal
import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_TaylorWiles_finrank_inf_traceZero_of_hasDistinctRationalEigenvalues

open Module TaylorWiles

universe u
theorem TaylorWiles.finrank_inf_traceZero_of_hasDistinctRationalEigenvalues {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) k} (hM : M.HasDistinctRationalEigenvalues) :
    finrank k (LinearMap.ker (TaylorWiles.adAction M) ⊓ TaylorWiles.traceZero k : Submodule k (Matrix (Fin 2) (Fin 2) k)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_TaylorWiles_finrank_inf_traceZero_of_hasDistinctRationalEigenvalues.solution
