import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_forall_subst_addVia_act_of_finrank_eq_two
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_primitives_mod_nthSeries_typed_forall_subst_addVia_act_of_finrank_eq_two
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hdim : ∃ e e' : MvPowerSeries (Fin 2) k,
      MvPowerSeries.constantCoeff e = 0 ∧ MvPowerSeries.constantCoeff e' = 0 ∧
      X₀.F.addCoboundary e ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) ∧
      X₀.F.addCoboundary e' ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) ∧
      (∀ c c' : k, c • e + c' • e' ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) → c = 0 ∧ c' = 0) ∧
      (∀ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 →
        X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l)))) →
        ∃ c c' : k, g - (c • e + c' • e') ∈ Ideal.span (Set.range (X₀.F.nthSeries q)))) :
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k,
      (∀ i, MvPowerSeries.constantCoeff (g i) = 0) ∧
      (∀ i, X₀.F.addCoboundary (g i) ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.F.nthSeries q l))))) ∧
      (∀ c : Fin 2 → k, (∑ i, c i • g i) ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) → c = 0) ∧
      (∀ a : Zp2 q,
        MvPowerSeries.subst (X₀.act a) (g 0) - j₀ a • g 0 ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
        MvPowerSeries.subst (X₀.act a) (g 1) - j₀ (WittVector.frobenius a) • g 1 ∈
          Ideal.span (Set.range (X₀.F.nthSeries q))) ∧
      (∀ α β : Zp2 q, ∃ c : Fin 2 → k,
        MvPowerSeries.subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 0)
            - (j₀ α • g 0 + c 0 • g 1) ∈ Ideal.span (Set.range (X₀.F.nthSeries q)) ∧
        MvPowerSeries.subst (Series.addVia X₀.F (X₀.act α) ((X₀.act β).comp X₀.varpi)) (g 1)
            - (j₀ (WittVector.frobenius α) • g 1 + c 1 • g 0) ∈ Ideal.span (Set.range (X₀.F.nthSeries q))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_forall_subst_addVia_act_of_finrank_eq_two.solution
