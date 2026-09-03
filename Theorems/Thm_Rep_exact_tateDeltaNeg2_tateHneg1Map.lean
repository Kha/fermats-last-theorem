import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import P2M.Util
import P2M.Sol.S_Rep_exact_tateDeltaNeg2_tateHneg1Map

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.exact_tateDeltaNeg2_tateHneg1Map {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδneg2 hX) (Rep.tateHneg1Map X.f) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_tateDeltaNeg2_tateHneg1Map.solution
