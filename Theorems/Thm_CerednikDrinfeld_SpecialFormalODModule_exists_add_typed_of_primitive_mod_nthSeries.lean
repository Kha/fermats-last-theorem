import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_add_typed_of_primitive_mod_nthSeries
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (h : MvPowerSeries (Fin 2) k) (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hh : X₀.F.addCoboundary h ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))))) :
    ∃ h₀ h₁ : MvPowerSeries (Fin 2) k,
      MvPowerSeries.constantCoeff h₀ = 0 ∧ MvPowerSeries.constantCoeff h₁ = 0 ∧
      X₀.F.addCoboundary h₀ ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) ∧
      X₀.F.addCoboundary h₁ ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) ∧
      h - (h₀ + h₁) ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
      (∀ a : Zp2 q,
        MvPowerSeries.subst (X₀.act a) h₀ - j₀ a • h₀ ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
        MvPowerSeries.subst (X₀.act a) h₁ - j₀ (WittVector.frobenius a) • h₁ ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_add_typed_of_primitive_mod_nthSeries.solution
