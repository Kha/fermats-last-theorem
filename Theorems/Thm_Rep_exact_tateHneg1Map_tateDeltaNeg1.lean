import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import P2M.Util
import P2M.Sol.S_Rep_exact_tateHneg1Map_tateDeltaNeg1

set_option autoImplicit false
universe u v w
open CategoryTheory Rep
theorem Rep.exact_tateHneg1Map_tateDeltaNeg1 {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{w} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateHneg1Map X.g) (Rep.tateδneg1 hX) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_tateHneg1Map_tateDeltaNeg1.solution
