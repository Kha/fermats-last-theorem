import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field

set_option autoImplicit false

universe u v w

theorem Module.FaithfullyFlat.of_forall_isMaximal_exists_ringHom_field
    {B : Type u} {S : Type v} [CommRing B] [CommRing S] [Algebra B S] [Module.Flat B S]
    (h : ∀ m : Ideal B, m.IsMaximal →
      ∃ (K : Type w) (_ : Field K) (ψ : S →+* K), m ≤ RingHom.ker (ψ.comp (algebraMap B S))) :
    Module.FaithfullyFlat B S := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field.solution
