import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierNModule
import Definitions.Def_CerednikDrinfeld_CartierLMapFibre
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) :
    (∀ n : ℕ, CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j n ∨
        Φ.IsPiBijective j n) ∧
      (CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j 0 ∨
        CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j 1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field.solution
