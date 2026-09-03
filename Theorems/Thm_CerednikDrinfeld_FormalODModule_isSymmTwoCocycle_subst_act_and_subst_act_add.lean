import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ

    (∀ φ : Fin 2 → MvPowerSeries (Fin 2) k, (φ = X₀.varpi ∨ ∃ a, φ = X₀.act a) →
      (∀ Γ, X₀.F.IsSymmTwoCocycle Γ → X₀.F.IsSymmTwoCocycle (pull φ Γ)) ∧
      (∀ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 →
        MvPowerSeries.constantCoeff (MvPowerSeries.subst φ g) = 0 ∧
        pull φ (X₀.F.addCoboundary g) = X₀.F.addCoboundary (MvPowerSeries.subst φ g))) ∧

    (∀ (a b : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      pull (X₀.act (a * b)) Γ = pull (X₀.act b) (pull (X₀.act a) Γ)) ∧
    (∀ Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, pull (X₀.act 1) Γ = Γ) ∧

    (∀ (a b : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k), X₀.F.IsSymmTwoCocycle Γ →
      ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull (X₀.act (a + b)) Γ = pull (X₀.act a) Γ + pull (X₀.act b) Γ + X₀.F.addCoboundary g) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add.solution
