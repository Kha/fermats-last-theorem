import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_map_mem_setOf_invariant_of_mem

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.map_mem_setOf_invariant_of_mem
    (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] (X : FormalODModule p R)
    (J : Ideal (MvPowerSeries (Fin 2) R)) (ψ : R →+* R') (w : MvPowerSeries (Fin 2) R)
    (hw : w ∈ {w : MvPowerSeries (Fin 2) R | w ∈ J ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) '' (J : Set (MvPowerSeries (Fin 2) R)))}) :
    MvPowerSeries.map ψ w ∈ {w : MvPowerSeries (Fin 2) R' | w ∈ (J.map (MvPowerSeries.map ψ)) ∧
          MvPowerSeries.subst (X.map ψ).F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R')) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R'))) '' ((J.map (MvPowerSeries.map ψ)) : Set (MvPowerSeries (Fin 2) R')))} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_map_mem_setOf_invariant_of_mem.solution
