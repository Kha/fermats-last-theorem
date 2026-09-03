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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_one_of_lieOne_le_ker_lieVarpi
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (j : Zp2 p →+* B) (X : FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j))
    (h : X.lieOne j ≤ LinearMap.ker X.lieVarpi)
    {B' : Type} [CommRing B'] [CharP B' p] (f : B →+* B') :
    FormalODModule.CritChart.IsCritical (X.map f) (f.comp j) 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi.solution
