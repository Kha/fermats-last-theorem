import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] (X₀ : FormalODModule q k) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    let Θ : MvPowerSeries (Fin 2 ⊕ Fin 2) k → MvPowerSeries (Fin 2) k := fun Γ =>
      ∑ i ∈ Finset.range q,
        MvPowerSeries.subst (Sum.elim (X₀.F.nthSeries i) fun l => MvPowerSeries.X l) Γ
    (∀ (c : k) (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k), Θ (c • Γ + Γ') = c • Θ Γ + Θ Γ') ∧
    (∀ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 →
      Θ (X₀.F.addCoboundary g) = MvPowerSeries.subst (X₀.F.nthSeries q) g) ∧
    (∀ (a : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      Θ (pull (X₀.act a) Γ) = MvPowerSeries.subst (X₀.act a) (Θ Γ)) ∧
    (∀ Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, Θ (pull X₀.varpi Γ) = MvPowerSeries.subst X₀.varpi (Θ Γ)) ∧
    (∀ Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, X₀.F.IsSymmTwoCocycle Γ →
      X₀.F.addCoboundary (Θ Γ) = pull (X₀.F.nthSeries q) Γ) ∧
    (∀ (φ : Fin 2 → MvPowerSeries (Fin 2) k) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → MvPowerSeries.constantCoeff Γ = 0 →
      pull φ Γ ∈ Ideal.span (Set.range (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.solution
