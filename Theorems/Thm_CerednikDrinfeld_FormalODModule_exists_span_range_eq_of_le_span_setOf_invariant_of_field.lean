import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_span_range_eq_of_le_span_setOf_invariant_of_field

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_span_range_eq_of_le_span_setOf_invariant_of_field
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ]
    (X : FormalODModule p κ) (I : Ideal (MvPowerSeries (Fin 2) κ))
    (hfin : Module.Finite κ (MvPowerSeries (Fin 2) κ ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) ^ q ∈ I)
    (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)
    (hgen : I ≤ Ideal.span {w : MvPowerSeries (Fin 2) κ | w ∈ I ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ))) '' (I : Set (MvPowerSeries (Fin 2) κ)))}) :
    ∃ u : Series κ,
      (∀ j, MvPowerSeries.constantCoeff (u j) = 0) ∧
      (∀ j, MvPowerSeries.subst X.F.toPowerSeries (u j) - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) (u j) ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ))) '' (I : Set (MvPowerSeries (Fin 2) κ)))) ∧
      Ideal.span (Set.range u) = I := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_span_range_eq_of_le_span_setOf_invariant_of_field.solution
