import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Theorems.Thm_IharaLemma_isLocalizedModule_toCorner
import P2M.Util
namespace P2MW.S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal

open IharaLemma

theorem solution {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n) {M : Type}
    [AddCommGroup M] [Module B M] :
    IsLocalizedModule (S.𝔪 i).primeCompl (toCorner (M := M) (S.e i)) :=
  IharaLemma.isLocalizedModule_toCorner (S.idem i) (S.𝔪 i) (S.notMem i)
    (S.mem_of_isMaximal_of_ne i)
