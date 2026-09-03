import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (h𝒯 : 𝒯.IsTree)
    (Γ : Subgroup G)
    (hstab : ∀ w : W, Finite (MulAction.stabilizer (↥Γ) w))
    (hV : Finite (QuotVert (↥Γ) W)) (hE : Finite (QuotEdge (↥Γ) 𝒯))
    (hinv : ∀ g ∈ Γ, ∀ d : 𝒯.Dart, g • d ≠ d.symm)
    (N : Subgroup G) (hle : N ≤ Γ) (hidx : N.relIndex Γ ≠ 0)
    (htf : ∀ g ∈ N, IsOfFinOrder g → g = 1) :
    IsSchottky (↥N) 𝒯 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one.solution
