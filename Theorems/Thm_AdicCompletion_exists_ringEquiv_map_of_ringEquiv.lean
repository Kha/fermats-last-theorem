import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringEquiv_map_of_ringEquiv

set_option autoImplicit false

universe u v

theorem AdicCompletion.exists_ringEquiv_map_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (I : Ideal R) (e : R ≃+* S) :
    ∃ ê : AdicCompletion I R ≃+* AdicCompletion (I.map e) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion (I.map e) S) (e r) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringEquiv_map_of_ringEquiv.solution
