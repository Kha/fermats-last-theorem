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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) (i : ℕ)
    (hi : CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j i) :
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Φ.F,
      (∀ r, e r ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants Φ.toFormalODModule j i) ∧
      (∀ m ∈ Φ.gradedPiece j i, ∃! w : Fin 2 → WittVector p k, m = ∑ r, w r • e r) ∧
      (∀ w : Fin 2 → WittVector p k,
        (∑ r, w r • e r) ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants Φ.toFormalODModule j i ↔
          ∀ r, WittVector.frobenius (w r) = w r) ∧
      (∀ m ∈ Φ.gradedPiece j i, ∃ g ∈ Φ.gradedPiece j i,
        MvFormalGroup.CartierModule.endAct Φ.varpiEnd m = MvFormalGroup.CartierModule.verschiebung g) ∧
      (∀ g ∈ Φ.gradedPiece j i, ∃ m ∈ Φ.gradedPiece j i,
        MvFormalGroup.CartierModule.verschiebung g = MvFormalGroup.CartierModule.endAct Φ.varpiEnd m) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical.solution
