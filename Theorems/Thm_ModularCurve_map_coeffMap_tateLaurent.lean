import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_map_coeffMap_tateLaurent

open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.map_coeffMap_tateLaurent (K : Type*) [CommRing K] (K' : Type*) [CommRing K']
    (f : K →+* K') : (tateLaurent K).map (coeffMap f) = tateLaurent K' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_map_coeffMap_tateLaurent.solution
