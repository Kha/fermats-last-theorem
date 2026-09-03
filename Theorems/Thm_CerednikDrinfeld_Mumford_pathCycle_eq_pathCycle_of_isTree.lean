import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_pathCycle_eq_pathCycle_of_isTree

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.pathCycle_eq_pathCycle_of_isTree
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree) [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯)
    (v₀ v₁ : W) (g : G) :
    pathCycle 𝒯 orb v₁ g = pathCycle 𝒯 orb v₀ g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_pathCycle_eq_pathCycle_of_isTree.solution
