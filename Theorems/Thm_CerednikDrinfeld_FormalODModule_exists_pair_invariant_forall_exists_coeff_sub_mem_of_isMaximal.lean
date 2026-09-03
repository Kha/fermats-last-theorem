import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open scoped BigOperators

theorem CerednikDrinfeld.FormalODModule.exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsNoetherianRing R]
    (X : FormalODModule p R) (J : Ideal (MvPowerSeries (Fin 2) R))
    (hfin : Module.Finite R (MvPowerSeries (Fin 2) R ⧸ J))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ q ∈ J)
    (hunit : ∀ f ∈ J, MvPowerSeries.constantCoeff f = 0)
    (hInv : J = Ideal.span {w : MvPowerSeries (Fin 2) R | w ∈ J ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) '' (J : Set (MvPowerSeries (Fin 2) R)))})
    (𝔫 : Ideal R) (h𝔫 : 𝔫.IsMaximal) :
    ∃ r : Fin 2 → MvPowerSeries (Fin 2) R,
      (∀ j, r j ∈ {w : MvPowerSeries (Fin 2) R | w ∈ J ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) '' (J : Set (MvPowerSeries (Fin 2) R)))}) ∧
      ∀ f ∈ J, ∃ (a b : Fin 2 → MvPowerSeries (Fin 2) R), (∀ i, b i ∈ J) ∧
        ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d (f - (∑ j, a j * r j + ∑ i, MvPowerSeries.X i * b i)) ∈ 𝔫 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal.solution
