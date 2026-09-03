import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
namespace P2MW.S_WeierstrassCurve_card_pos

theorem solution {F : Type*} [CommRing F] [Finite F]
    (W : WeierstrassCurve F) : 0 < W.card :=
  Nat.card_pos
