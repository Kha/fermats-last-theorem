import Mathlib
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_IdempotentSplitting_exists_basis_cornerSubmodule_coe_eq_smul

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.exists_basis_cornerSubmodule_coe_eq_smul
    {B : Type} [CommRing B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    {M : Type} [AddCommGroup M] [Module B M] {ι : Type} (b : Module.Basis ι B M) :
    ∃ bj : Module.Basis ι (S.CornerRing i) ↥(IharaLemma.cornerSubmodule (M := M) (S.e i)),
      ∀ k : ι, ((bj k : IharaLemma.cornerSubmodule (M := M) (S.e i)) : M) = S.e i • b k := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_IdempotentSplitting_exists_basis_cornerSubmodule_coe_eq_smul.solution
