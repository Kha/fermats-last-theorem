import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.Algebra.Module.LocalizedModule.Basic
import P2M.Util
import P2M.Sol.S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.isLocalizedModule_toCorner_maximalIdeal {B : Type}
    [CommRing B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n) {M : Type}
    [AddCommGroup M] [Module B M] :
    IsLocalizedModule (S.𝔪 i).primeCompl (IharaLemma.toCorner (M := M) (S.e i)) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal.solution
