import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_card_pos

theorem WeierstrassCurve.card_pos {F : Type*} [CommRing F] [Finite F]
    (W : WeierstrassCurve F) : 0 < W.card := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_card_pos.solution
