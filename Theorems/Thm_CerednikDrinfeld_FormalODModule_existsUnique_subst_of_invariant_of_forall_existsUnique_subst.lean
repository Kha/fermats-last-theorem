import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_existsUnique_subst_of_invariant_of_forall_existsUnique_subst

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.existsUnique_subst_of_invariant_of_forall_existsUnique_subst
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
    (hcoord : ∀ w : MvPowerSeries (Fin 2) B,
      MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2) B, MvPowerSeries.subst u W = w) :
    ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
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
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_subst_of_invariant_of_forall_existsUnique_subst.solution
