import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_isBaseChange

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.exists_isBaseChange
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) :
    ∃ G : FormalGroup S, F.IsBaseChange f G := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_isBaseChange.solution
