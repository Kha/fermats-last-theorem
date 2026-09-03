import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hconn : 𝒯.Connected)
    (hstab : ∀ w : W, Finite (MulAction.stabilizer G w))
    (hV : Finite (QuotVert G W)) (hE : Finite (QuotEdge G 𝒯)) :
    Group.FG G := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge.solution
