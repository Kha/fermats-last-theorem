import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_LawHom_exists_isBaseChange_series_eq_map

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.LawHom.exists_isBaseChange_series_eq_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {F G : FormalGroup R}
    (θ : FormalGroup.LawHom F G) (F' G' : FormalGroup S)
    (hF : F.IsBaseChange f F') (hG : G.IsBaseChange f G') :
    ∃ θ' : FormalGroup.LawHom F' G', θ'.series = PowerSeries.map f θ.series := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_LawHom_exists_isBaseChange_series_eq_map.solution
