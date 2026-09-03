import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_subst_mem_span_of_isODHom
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.subst_mem_span_of_isODHom
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (Φ Y : FormalODModule p B)
    (ρ : Series B) (hρ : FormalODModule.IsODHom Φ Y ρ) :
    (∀ (a : Zp2 p) (G : MvPowerSeries (Fin 2) B), G ∈ Ideal.span (Set.range ρ) →
      MvPowerSeries.subst (Φ.act a) G ∈ Ideal.span (Set.range ρ)) ∧
    (∀ G : MvPowerSeries (Fin 2) B, G ∈ Ideal.span (Set.range ρ) →
      MvPowerSeries.subst Φ.varpi G ∈ Ideal.span (Set.range ρ)) ∧
    (∀ G : MvPowerSeries (Fin 2) B, G ∈ Ideal.span (Set.range ρ) →
      MvPowerSeries.subst Φ.F.toPowerSeries G ∈
        Ideal.span (Set.range (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j)) ∪
          Set.range (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j)))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_subst_mem_span_of_isODHom.solution
