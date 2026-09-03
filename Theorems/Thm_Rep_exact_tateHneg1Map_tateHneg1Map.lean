import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_exact_tateHneg1Map_tateHneg1Map

set_option autoImplicit false
universe u v w
open CategoryTheory Rep
theorem Rep.exact_tateHneg1Map_tateHneg1Map {k G : Type*} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateHneg1Map X.f) (Rep.tateHneg1Map X.g) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_tateHneg1Map_tateHneg1Map.solution
