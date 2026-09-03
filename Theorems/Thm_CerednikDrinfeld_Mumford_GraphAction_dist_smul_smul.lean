import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.Combinatorics.SimpleGraph.Metric
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul

set_option autoImplicit false

theorem CerednikDrinfeld.Mumford.GraphAction.dist_smul_smul
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
    [CerednikDrinfeld.Mumford.GraphAction G 𝒯] (g : G) (x y : W) :
    𝒯.dist (g • x) (g • y) = 𝒯.dist x y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul.solution
