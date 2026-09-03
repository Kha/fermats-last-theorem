import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq

set_option autoImplicit false

theorem RingHom.eq_of_forall_exists_sub_mem_pow_of_comp_eq
    (R Rh S : Type) [CommRing R] [CommRing Rh] [CommRing S]
    (ι : R →+* Rh) (I : Ideal Rh)
    (hdense : ∀ (x : Rh) (n : ℕ), ∃ r : R, x - ι r ∈ I ^ n)
    (J : Ideal S) [IsHausdorff J S]
    (G H : Rh →+* S) (hG : ∀ x ∈ I, G x ∈ J) (hH : ∀ x ∈ I, H x ∈ J)
    (h : G.comp ι = H.comp ι) :
    G = H := by p2m_exact_reverting @_root_.P2MW.S_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq.solution
