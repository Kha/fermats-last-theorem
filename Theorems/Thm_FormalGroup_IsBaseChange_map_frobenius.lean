import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsBaseChange_map_frobenius

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.IsBaseChange.map_frobenius
    {R S : Type u} [CommRing R] [CommRing S] (q : ℕ) [Fact q.Prime] [CharP R q] [CharP S q]
    (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S) (h : F.IsBaseChange f G) :
    (F.map (frobenius R q)).IsBaseChange f (G.map (frobenius S q)) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsBaseChange_map_frobenius.solution
