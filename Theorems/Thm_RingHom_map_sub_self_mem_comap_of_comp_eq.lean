import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_map_sub_self_mem_comap_of_comp_eq

set_option autoImplicit false

theorem RingHom.map_sub_self_mem_comap_of_comp_eq
    {C C' : Type} [CommRing C] [CommRing C'] (c : C →+* C') (τ : C →+* C) (τ' : C' →+* C')
    (hcomm : τ'.comp c = c.comp τ) (y' : Ideal C')
    (hfix : ∀ a : C, τ' (c a) - c a ∈ y') (a : C) :
    τ a - a ∈ Ideal.comap c y' := by p2m_exact_reverting @_root_.P2MW.S_RingHom_map_sub_self_mem_comap_of_comp_eq.solution
