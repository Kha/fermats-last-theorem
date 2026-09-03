import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_tateBase_map_coeffMap

set_option autoImplicit false

theorem ModularCurve.tateBase_map_coeffMap {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') (N : ℕ) [NeZero N] :
    (ModularCurve.tateBase K N).map (ModularCurve.coeffMap f) = ModularCurve.tateBase K' N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tateBase_map_coeffMap.solution
