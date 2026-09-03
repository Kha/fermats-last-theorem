import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot

set_option autoImplicit false

universe u
theorem AlgHom.bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot
    {T' : Type u} [CommRing T'] (I : Ideal T') (hI2 : I * I = ⊥)
    (C : Type u) [CommRing C] [Algebra T' C]
    (ψ : C →ₐ[T'] C) (hψ : ∀ c : C, ψ c - c ∈ I.map (algebraMap T' C)) :
    Function.Bijective ψ ∧ ∀ p : PrimeSpectrum C, PrimeSpectrum.comap ψ.toRingHom p = p := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot.solution
