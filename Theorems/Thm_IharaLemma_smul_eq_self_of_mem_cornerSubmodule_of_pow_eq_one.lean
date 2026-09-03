import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one

set_option autoImplicit false

theorem IharaLemma.smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one
    {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n) (t : B) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : B)) (ht : t ^ n = 1) (h1 : t - 1 ∈ S.𝔪 i)
    (v : M) (hv : v ∈ IharaLemma.cornerSubmodule (M := M) (S.e i)) :
    t • v = v := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one.solution
