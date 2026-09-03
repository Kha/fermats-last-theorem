import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_IsTwoKernel_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot

set_option autoImplicit false
universe u
open ModularCurve

theorem WeierstrassCurve.IsTwoKernel.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (h2 : IsUnit (2 : T))
    (h' : Polynomial T') (hh' : (W.map π).IsTwoKernel h') :
    ∃! h : Polynomial T, h.map π = h' ∧ W.IsTwoKernel h := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_IsTwoKernel_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot.solution
