import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_isODHom_of_isLawHom_of_invariant_coordinates

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_isODHom_of_isLawHom_of_invariant_coordinates
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hact : ∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst (X.act a) f ∈ I)
    (hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I)
    (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
    (huinv : ∀ j, MvPowerSeries.subst X.F.toPowerSeries (u j) -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B))))
    (hdesc : ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w)
    (G : MvFormalGroup 2 B) (hGc : G.IsComm) (hG : IsLawHom X.F G u) :
    ∃ Y : FormalODModule p B, Y.F = G ∧ FormalODModule.IsODHom X Y u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_of_isLawHom_of_invariant_coordinates.solution
