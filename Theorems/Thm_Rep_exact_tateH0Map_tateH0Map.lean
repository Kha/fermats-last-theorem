import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_exact_tateH0Map_tateH0Map

set_option autoImplicit false
universe u v w
open CategoryTheory Rep
theorem Rep.exact_tateH0Map_tateH0Map {k G : Type*} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateH0Map X.f) (Rep.tateH0Map X.g) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exact_tateH0Map_tateH0Map.solution
