import Mathlib
import P2M.Util
namespace P2MW.S_RingHom_map_sub_self_mem_comap_of_comp_eq

set_option autoImplicit false

theorem solution
    {C C' : Type} [CommRing C] [CommRing C'] (c : C →+* C') (τ : C →+* C) (τ' : C' →+* C')
    (hcomm : τ'.comp c = c.comp τ) (y' : Ideal C')
    (hfix : ∀ a : C, τ' (c a) - c a ∈ y') (a : C) :
    τ a - a ∈ Ideal.comap c y' := by
  rw [Ideal.mem_comap, map_sub]
  have h := hfix a
  rwa [← RingHom.comp_apply, hcomm, RingHom.comp_apply] at h
