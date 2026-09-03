import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_shortExact_map_resFunctor

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.shortExact_map_resFunctor {k G H : Type u} [CommRing k] [Group G] [Group H] (f : H →* G)
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    (X.map (Rep.resFunctor f)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_map_resFunctor.solution
