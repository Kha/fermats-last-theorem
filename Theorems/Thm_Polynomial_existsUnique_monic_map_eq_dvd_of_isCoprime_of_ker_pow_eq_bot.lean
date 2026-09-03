import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot

set_option autoImplicit false

universe u

open Polynomial

theorem Polynomial.existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (f : Polynomial T) (g' k' : Polynomial T') (hg' : g'.Monic) (hcop : IsCoprime g' k')
    (hfac : f.map π = g' * k') :
    ∃! g : Polynomial T, g.Monic ∧ g.map π = g' ∧ g ∣ f := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot.solution
