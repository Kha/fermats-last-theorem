import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
    (p : ℕ) [Fact p.Prime] {R S : Type u} [CommRing R] [CommRing S] (π : R →+* S) (μ : ℕ)
    (hI : RingHom.ker π ^ (μ + 1) = ⊥) (n : ℕ) (hp : (p : R) ^ n = 0)
    (X Y : CerednikDrinfeld.FormalODModule p R) :
    (∀ φ ψ : CerednikDrinfeld.SpecialFormal.Series R, X.IsODHom Y φ → X.IsODHom Y ψ →
        φ.map π = ψ.map π →
        (Y.act ((p : CerednikDrinfeld.Zp2 p) ^ (n * μ))).comp φ =
          (Y.act ((p : CerednikDrinfeld.Zp2 p) ^ (n * μ))).comp ψ) ∧
    (∀ φ : CerednikDrinfeld.SpecialFormal.Series R, (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
        (X.map π).IsODHom (Y.map π) (φ.map π) →
        X.IsODHom Y ((Y.act ((p : CerednikDrinfeld.Zp2 p) ^ (n * μ))).comp φ)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot.solution
