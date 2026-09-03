import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (Y : FormalODModule p K) (hY : Y.IsSpecial j) (hY4 : Y.HasHeight 4)
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hL : (Y.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (h1 : FormalODModule.CritChart.IsCritical Y j 1)
    (c : ℤ_[p] →+* WittVector p K) :
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Y.F,
      (∀ r, e r ∈ FormalODModule.CritChart.invariants Y j 1) ∧
      (∀ m ∈ Y.gradedPiece j 1, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r) ∧
      (∀ z, z ∈ (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1 ↔
        ∃ a : Fin 2 → ℤ_[p], z = (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0)) ∧
      (∀ a a' : Fin 2 → ℤ_[p],
        (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0) =
          (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a' r) • e r, 0) → a = a') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed.solution
