import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_iff_le_ker_lieVarpi_of_isSpecial
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

theorem CerednikDrinfeld.FormalODModule.CritChart.isCritical_iff_le_ker_lieVarpi_of_isSpecial
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [CharP K p]
    (j : CerednikDrinfeld.Zp2 p →+* K) (X : CerednikDrinfeld.FormalODModule p K)
    (hX : X.IsSpecial j) :
    (CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 0 ↔
        X.lieZero j ≤ LinearMap.ker X.lieVarpi) ∧
    (CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 1 ↔
        X.lieOne j ≤ LinearMap.ker X.lieVarpi) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_iff_le_ker_lieVarpi_of_isSpecial.solution
