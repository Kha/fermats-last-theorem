import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    {ι : Type} [Fintype ι] (bC : Module.Basis ι B (MvPowerSeries (Fin 2) B ⧸ I))
    (b : ι → MvPowerSeries (Fin 2) B) (hb : ∀ k, Ideal.Quotient.mk I (b k) = bC k)
    {m : ℕ} (u : Fin m → MvPowerSeries (Fin 2) B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
    (huinv : ∀ j, MvPowerSeries.subst X.F.toPowerSeries (u j) - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    (huI : Ideal.span (Set.range u) = I) :
    (∀ f : MvPowerSeries (Fin 2) B, ∃ c : ι → MvPowerSeries (Fin m) B,
        f = ∑ k, MvPowerSeries.subst u (c k) * b k) ∧
    (∀ c : ι → MvPowerSeries (Fin m) B,
        ∑ k, MvPowerSeries.subst u (c k) * b k = 0 → ∀ k, MvPowerSeries.subst u (c k) = 0) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant.solution
