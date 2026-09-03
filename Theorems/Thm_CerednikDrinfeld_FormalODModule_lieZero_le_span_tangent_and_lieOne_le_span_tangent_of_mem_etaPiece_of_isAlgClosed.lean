import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
attribute [-instance] MvFormalGroup.instIsCommMapRingHom instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K] [CharP K p] (j : Zp2 p →+* K)
    (X : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    X.lieZero j ≤ Submodule.span K (MvFormalGroup.CartierModule.tangent ''
        {a : MvFormalGroup.CartierModule p X.F |
          ∃ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0,
            (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ a}) ∧
    X.lieOne j ≤ Submodule.span K (MvFormalGroup.CartierModule.tangent ''
        {a : MvFormalGroup.CartierModule p X.F |
          ∃ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1,
            (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ a}) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed.solution
