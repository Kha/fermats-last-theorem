import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsBaseChange_nthSeries_eq_map

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsBaseChange.nthSeries_eq_map
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S)
    (h : F.IsBaseChange f G) (n : ℕ) :
    G.nthSeries n = PowerSeries.map f (F.nthSeries n) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsBaseChange_nthSeries_eq_map.solution
