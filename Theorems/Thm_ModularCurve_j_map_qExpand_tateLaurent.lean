import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_ModularCurve_j_map_qExpand_tateLaurent

open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.j_map_qExpand_tateLaurent (K : Type*) [CommRing K] (N : ℕ) [NeZero N] :
    ((tateLaurent K).map (qExpand K N)).j = jqNModC K N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_j_map_qExpand_tateLaurent.solution
