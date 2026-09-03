import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map

set_option autoImplicit false

open PowerSeries

theorem WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map
    {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) :
    (W.map f).formalW = PowerSeries.map f W.formalW ∧
      (W.map f).formalGroupLawFixed = MvPowerSeries.map f W.formalGroupLawFixed := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map.solution
