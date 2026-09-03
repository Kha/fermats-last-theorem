import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsBaseChange_invDiff_eq_map

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.IsBaseChange.invDiff_eq_map
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S)
    (hG : F.IsBaseChange f G) :
    G.invDiff = PowerSeries.map f F.invDiff := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsBaseChange_invDiff_eq_map.solution
