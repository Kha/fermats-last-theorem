import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_conj_of_subst_eq_X
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_conj_of_subst_eq_X
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (α β : Fin 2 → MvPowerSeries (Fin 2) k)
    (hα0 : ∀ i, MvPowerSeries.constantCoeff (α i) = 0) (hβ0 : ∀ i, MvPowerSeries.constantCoeff (β i) = 0)
    (hαβ : ∀ i, MvPowerSeries.subst α (β i) = MvPowerSeries.X i)
    (hβα : ∀ i, MvPowerSeries.subst β (α i) = MvPowerSeries.X i) :
    ∃ X₁ : SpecialFormalODModule q j₀,
      (∀ i, X₁.F.toPowerSeries i =
        MvPowerSeries.subst
          (fun j => MvPowerSeries.subst
            (Sum.elim
              (fun m => MvPowerSeries.subst
                (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (α m))
              fun m => MvPowerSeries.subst
                (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (α m))
            (X₀.F.toPowerSeries j))
          (β i)) ∧
      (∀ a, X₁.act a = Series.comp β (Series.comp (X₀.act a) α)) ∧
      X₁.varpi = Series.comp β (Series.comp X₀.varpi α) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_conj_of_subst_eq_X.solution
