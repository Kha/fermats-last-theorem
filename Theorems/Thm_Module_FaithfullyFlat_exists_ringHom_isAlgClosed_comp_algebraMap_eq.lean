import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq

set_option autoImplicit false

universe u

theorem Module.FaithfullyFlat.exists_ringHom_isAlgClosed_comp_algebraMap_eq
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (k : Type u) [Field k] (sk : S →+* k) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (j : k →+* K) (sK : S' →+* K),
      sK.comp (algebraMap S S') = j.comp sk := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq.solution
