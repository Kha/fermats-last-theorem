import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed

set_option autoImplicit false

universe u

theorem Module.FaithfullyFlat.exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    [Module.FaithfullyFlat S S'] [Algebra.FiniteType S S']
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    ∃ σ : S' →+* k, σ.comp (algebraMap S S') = sk := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed.solution
