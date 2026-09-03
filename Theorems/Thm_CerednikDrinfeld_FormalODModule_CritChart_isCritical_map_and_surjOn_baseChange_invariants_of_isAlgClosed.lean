import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed
attribute [-instance] CerednikDrinfeld.GradedCartierModuleData.module CerednikDrinfeld.GradedCartierModuleData.addCommGroup instTopologicallyFGOfFiniteType
attribute [-simp] CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] {k K : Type u} [Field k] [IsAlgClosed k] [CharP k p]
    [Field K] [IsAlgClosed K] [CharP K p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (X : CerednikDrinfeld.FormalODModule p k)
    (hX : X.IsSpecial j) (hX4 : X.HasHeight 4) (g : k →+* K) (i : ℕ)
    (hi : CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j i) :
    CerednikDrinfeld.FormalODModule.CritChart.IsCritical (X.map g) (g.comp j) i ∧
    (∀ m ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants X j i,
      MvFormalGroup.CartierModule.baseChange (Φ := X.F) g m ∈
        CerednikDrinfeld.FormalODModule.CritChart.invariants (X.map g) (g.comp j) i) ∧
    (∀ m' ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants (X.map g) (g.comp j) i,
      ∃ m ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants X j i,
        MvFormalGroup.CartierModule.baseChange (Φ := X.F) g m = m') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed.solution
