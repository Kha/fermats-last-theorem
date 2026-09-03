import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isODHom_of_comp_eq_act_pow_of_subst_injective

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.isODHom_of_comp_eq_act_pow_of_subst_injective
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (X Y : FormalODModule p B) (ρ β : Series B) (N : ℕ)
    (hρ : FormalODModule.IsODHom X Y ρ)
    (hinj : ∀ H H' : MvPowerSeries (Fin 2) B, MvPowerSeries.subst ρ H = MvPowerSeries.subst ρ H' → H = H')
    (hinj2 : ∀ H H' : MvPowerSeries (Fin 2 ⊕ Fin 2) B,
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))) H =
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))) H' → H = H')
    (hβ0 : ∀ i, MvPowerSeries.constantCoeff (β i) = 0)
    (hβρ : β.comp ρ = X.act ((p : Zp2 p) ^ N)) :
    FormalODModule.IsODHom Y X β := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isODHom_of_comp_eq_act_pow_of_subst_injective.solution
