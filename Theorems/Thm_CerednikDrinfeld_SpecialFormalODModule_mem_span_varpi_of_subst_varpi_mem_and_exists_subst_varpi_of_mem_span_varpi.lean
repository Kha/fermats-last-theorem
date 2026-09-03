import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_mem_span_varpi_of_subst_varpi_mem_and_exists_subst_varpi_of_mem_span_varpi
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.mem_span_varpi_of_subst_varpi_mem_and_exists_subst_varpi_of_mem_span_varpi
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) :
    (∀ h : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff h = 0 →
        X₀.F.addCoboundary h ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi l)))) →
        MvPowerSeries.subst X₀.varpi h ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) →
        h ∈ Ideal.span (Set.range X₀.varpi)) ∧
    (∀ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 →
        X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) →
        g ∈ Ideal.span (Set.range X₀.varpi) →
        ∃ h : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff h = 0 ∧
          X₀.F.addCoboundary h ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi l)))) ∧
          g - MvPowerSeries.subst X₀.varpi h ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_mem_span_varpi_of_subst_varpi_mem_and_exists_subst_varpi_of_mem_span_varpi.solution
