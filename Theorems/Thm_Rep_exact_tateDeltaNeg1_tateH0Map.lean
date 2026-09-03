import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import P2M.Util
import P2M.Sol.S_Rep_exact_tateDeltaNeg1_tateH0Map

set_option autoImplicit false
universe u v w
open CategoryTheory Rep
theorem Rep.exact_tateDeltaNeg1_tateH0Map {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{w} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδneg1 hX) (Rep.tateH0Map X.f) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_tateDeltaNeg1_tateH0Map.solution
