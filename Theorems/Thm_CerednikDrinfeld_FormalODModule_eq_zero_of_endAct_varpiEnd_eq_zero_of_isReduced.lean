import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
attribute [-instance] MvFormalGroup.instIsCommMapRingHom instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] [IsReduced B] (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (m : MvFormalGroup.CartierModule p X.F) (hm : MvFormalGroup.CartierModule.endAct X.varpiEnd m = 0) :
    m = 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced.solution
