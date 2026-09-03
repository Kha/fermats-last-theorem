import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_map_jqNModC

open ModularCurve
theorem ModularCurve.map_jqNModC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ℕ) [NeZero N] : coeffMap φ (jqNModC R N) = jqNModC S N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_map_jqNModC.solution
